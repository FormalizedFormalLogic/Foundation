import Foundation.FirstOrder.Basic
import Foundation.FirstOrder.Completeness.Corollaries
import Foundation.Vorspiel.ExistsUnique

/-!
# Translation and interpretation

-/

namespace LO.FirstOrder

@[ext]
structure Translation {L : Language} [L.Eq] (T : Theory L) [𝐄𝐐 ⪯ T] (L' : Language) where
  domain : Semisentence L 1
  rel {k} : L'.Rel k → Semisentence L k
  func {k} : L'.Func k → Semisentence L (k + 1)
  domain_nonempty :
    T ⊢!. ∃' domain
  func_defined {k} (f : L'.Func k) :
    T ⊢!. ∀* ((Matrix.conj fun i ↦ domain/[#i]) ➝ ∃'! (domain/[#0] ⋏ func f))

namespace Translation

variable {L₁ L₂ : Language} [L₁.Eq] {T₁ : Theory L₁} [𝐄𝐐 ⪯ T₁]

variable (π : Translation T₁ L₂)

def fal (φ : Semiformula L₁ ξ (n + 1)) : Semiformula L₁ ξ n := ∀[Rew.emb ▹ π.domain/[#0]] φ

def exs (φ : Semiformula L₁ ξ (n + 1)) : Semiformula L₁ ξ n := ∃[Rew.emb ▹ π.domain/[#0]] φ

notation:64 "∀_[" π "] " ψ => fal π ψ
notation:64 "∃_[" π "] " ψ => exs π ψ

@[simp] lemma neg_fal (φ : Semiformula L₁ ξ (n + 1)) : ∼(∀_[π] φ) = ∃_[π] ∼φ := by simp [fal, exs]

@[simp] lemma neg_exs (φ : Semiformula L₁ ξ (n + 1)) : ∼(∃_[π] φ) = ∀_[π] ∼φ := by simp [fal, exs]

def varEqual : Semiterm L₂ ξ n → Semiformula L₁ ξ (n + 1)
  |                     #x => “z. z = #x.succ”
  |                     &x => “z. z = &x”
  | .func (arity := k) f v =>
    ∀^[k] (
      (Matrix.conj fun i ↦
        Rew.emb ▹ π.domain/[#(i.addCast (n + 1))] ⋏
        Rew.substs (#(i.addCast (n + 1)) :> fun j ↦ #((j.addNat 1).addNat k)) ▹ varEqual (v i))
      ➝ (Rew.embSubsts (#((0 : Fin (n + 1)).addNat k) :> fun i ↦ #(i.addCast (n + 1))) ▹ π.func f)
    )

def translateRel {k} (r : L₂.Rel k) (v : Fin k → Semiterm L₂ ξ n) : Semiformula L₁ ξ n :=
  ∀^[k] (
    (Matrix.conj fun i ↦
      Rew.emb ▹ π.domain/[#(i.addCast n)] ⋏
      Rew.substs (#(i.addCast n) :> fun j ↦ #(j.addNat k)) ▹ π.varEqual (v i))
    ➝ (Rew.embSubsts (fun i ↦ #(i.addCast n)) ▹ π.rel r)
  )

def translateAux {n} : Semiformula L₂ ξ n → Semiformula L₁ ξ n
  | .rel r v  => π.translateRel r v
  | .nrel r v => ∼π.translateRel r v
  |         ⊤ => ⊤
  |         ⊥ => ⊥
  |     φ ⋏ ψ => translateAux φ ⋏ translateAux ψ
  |     φ ⋎ ψ => translateAux φ ⋎ translateAux ψ
  |      ∀' φ => ∀_[π] translateAux φ
  |      ∃' φ => ∃_[π] translateAux φ

lemma translateAux_neg {n : ℕ} (φ : Semiformula L₂ ξ n) : π.translateAux (∼φ) = ∼π.translateAux φ := by
  induction φ using Semiformula.rec' <;> simp [translateAux, *, ←Semiformula.neg_eq]

def translate  : Semiformula L₂ ξ n →ˡᶜ Semiformula L₁ ξ n where
  toTr := π.translateAux
  map_top' := rfl
  map_bot' := rfl
  map_and' := fun _ _ ↦ rfl
  map_or' := fun _ _ ↦ rfl
  map_neg' := by simp [translateAux_neg]
  map_imply' := by simp [Semiformula.imp_eq, translateAux, translateAux_neg, ←Semiformula.neg_eq]

@[simp] lemma translate_rel {k} (R : L₂.Rel k) (v : Fin k → Semiterm L₂ ξ n) :
    π.translate (Semiformula.rel R v) = π.translateRel R v := rfl

@[simp] lemma translate_nrel {k} (R : L₂.Rel k) (v : Fin k → Semiterm L₂ ξ n) :
    π.translate (Semiformula.nrel R v) = ∼π.translateRel R v := rfl

@[simp] lemma translate_all (φ : Semiformula L₂ ξ (n + 1)) :
    π.translate (∀' φ) = ∀_[π] π.translate φ := rfl

@[simp] lemma translate_ex (φ : Semiformula L₂ ξ (n + 1)) :
    π.translate (∃' φ) = ∃_[π] π.translate φ := rfl

section semantics

open Semiformula

variable {M : Type u} [Structure L₁ M]

def Dom (x : M) : Prop := M ⊧/![x] π.domain

variable (M)

lemma dom_iff {x : M} : π.Dom x ↔ M ⊧/![x] π.domain := iff_of_eq rfl

abbrev Model := {x : M // π.Dom x}

@[simp] lemma pval_sub_domain (x : π.Model M) : M ⊧/![x] π.domain := x.prop

lemma domain_exists [Nonempty M] [M ⊧ₘ* T₁] : ∃ x : M, π.Dom x := by
  simpa [models₀_iff] using models_of_provable₀ (M := M) inferInstance π.domain_nonempty

@[simp] lemma coe_mem_domain (x : π.Model M) : π.Dom (x : M) := x.prop

@[simp] lemma eval_fal (φ : Semiformula L₁ ξ (n + 1)) :
    Evalm M e ε (∀_[π] φ) ↔ ∀ x : π.Model M, Evalm M (x :> e) ε φ := by
  simp [fal, ←dom_iff, Matrix.constant_eq_singleton]

@[simp] lemma eval_exs (φ : Semiformula L₁ ξ (n + 1)) :
    Evalm M e ε (∃_[π] φ) ↔ ∃ x : π.Model M, Evalm M (x :> e) ε φ := by
  simp [exs, ←dom_iff, Matrix.constant_eq_singleton]

variable [Nonempty M] [M ⊧ₘ* T₁] [Structure.Eq L₁ M]

lemma func_existsUnique_on_dom {k} (f : L₂.Func k) :
    ∀ (v : Fin k → M), (∀ i, π.Dom (v i)) → ∃! y, π.Dom y ∧ Evalbm M (y :> v) (π.func f) := by
  simpa [Dom, models_iff, eval_substs, Matrix.constant_eq_singleton] using
    models_of_provable₀ (M := M) inferInstance (π.func_defined f)

lemma func_existsUnique {k} (f : L₂.Func k) (v : Fin k → π.Model M) :
    ∃! y : π.Model M, M ⊧/(y :> fun i ↦ v i) (π.func f) := by
  have : ∃! y, π.Dom y ∧ M ⊧/(y :> fun i ↦ v i) (π.func f) :=
    π.func_existsUnique_on_dom M f (fun i ↦ v i) (fun i ↦ by simp [(v i).prop])
  rcases this.exists with ⟨y, hy, Hy⟩
  exact ExistsUnique.intro ⟨y, hy⟩ (by simpa using Hy) (by simpa using fun z hz Hz ↦ this.unique ⟨hz, Hz⟩ ⟨hy, Hy⟩)

variable {π M}

instance sub_nonempty : Nonempty (π.Model M) := by simpa using π.domain_exists M

noncomputable instance subStructure : Structure L₂ (π.Model M) where
  rel _ R v := Semiformula.Evalbm M (fun i ↦ (v i)) (π.rel R)
  func _ f v := Classical.choose! (π.func_existsUnique M f v)

lemma model_rel_iff {k} (r : L₂.Rel k) (v : Fin k → π.Model M) :
    Structure.rel r v ↔ Semiformula.Evalbm M (fun i ↦ (v i)) (π.rel r) := iff_of_eq rfl

lemma model_func_iff {k} (f : L₂.Func k) (y : π.Model M) (v : Fin k → π.Model M) :
    y = Structure.func f v ↔ Evalbm M (y :> fun i ↦ v i) (π.func f) := Classical.choose!_eq_iff _

lemma model_func_iff' {k} (f : L₂.Func k) (y : M) (v : Fin k → π.Model M) :
    y = Structure.func f v ↔ π.Dom y ∧ Evalbm M (y :> fun i ↦ v i) (π.func f) := by
  constructor
  · rintro rfl; simp [←model_func_iff]
  · intro h
    exact (π.func_existsUnique_on_dom M f (fun i ↦ v i) (by simp)).unique h (by simp [←model_func_iff])

lemma eval_varEqual_iff {t : Semiterm L₂ ξ n} {ε : ξ → π.Model M} {y : π.Model M} {x : Fin n → π.Model M} :
    Evalm M (y :> fun i ↦ x i) (fun x ↦ ε x) (π.varEqual t) ↔ y = Semiterm.valm (π.Model M) x ε t := by
  match t with
  |                     #_ => simp [varEqual, Subtype.coe_inj]
  |                     &_ => simp [varEqual, Subtype.coe_inj]
  | .func (arity := k) f v =>
    suffices
      (∀ w : Fin k → M,
        (∀ i, π.Dom (w i) ∧ Evalm M (w i :> fun i ↦ x i) (fun x ↦ ε x) (π.varEqual (v i))) →
          M ⊧/(y :> w) (π.func f)) ↔
      M ⊧/(y :> fun i ↦ (v i).valm (π.Model M) x ε) (π.func f) by
        simpa [varEqual, eval_embSubsts, Matrix.comp_vecCons', Matrix.constant_eq_singleton,
          Semiterm.val_func, model_func_iff, ←dom_iff]
    constructor
    · intro h; apply h
      intro i
      simp [eval_varEqual_iff (t := v i)]
    · intro h w hw
      suffices w = fun i ↦ ↑((v i).valm (π.Model M) x ε) by rcases this; exact h
      ext i
      let w' : π.Model M := ⟨w i, (hw i).1⟩
      have : Evalm M (w' :> fun i ↦ x i) (fun x ↦ ε x) (π.varEqual (v i)) := by simp [w', hw]
      simpa [w'] using congr_arg Subtype.val (eval_varEqual_iff.mp this)

lemma eval_translateRel_iff {n k} {ε : ξ → π.Model M} (e : Fin n → π.Model M) (R : L₂.Rel k) (v : Fin k → Semiterm L₂ ξ n) :
    Evalm M (fun i ↦ e i) (fun i ↦ ε i) (π.translateRel R v) ↔ Structure.rel R fun i ↦ Semiterm.valm (π.Model M) e ε (v i) := by
  suffices
    (∀ w, (∀ i, π.Dom (w i) ∧ (Evalm M (w i :> fun i ↦ ↑(e i)) fun i ↦ ↑(ε i)) (π.varEqual (v i))) → M ⊧/w (π.rel R)) ↔
    M ⊧/(fun i ↦ ↑((v i).valm (π.Model M) e ε)) (π.rel R) by
      simpa [translateRel, Matrix.comp_vecCons', model_rel_iff, eval_embSubsts, Matrix.constant_eq_singleton, ←dom_iff]
  constructor
  · intro h
    exact h (fun i ↦ ↑((v i).valm (π.Model M) e ε)) (fun i ↦ by simp [eval_varEqual_iff])
  · intro h w hw
    suffices w = fun i ↦ ↑((v i).valm (π.Model M) e ε) by rcases this; exact h
    ext i
    let w' : π.Model M := ⟨w i, (hw i).1⟩
    have : Evalm M (w' :> fun i ↦ e i) (fun x ↦ ε x) (π.varEqual (v i)) := by simp [w', hw]
    simpa [w'] using congr_arg Subtype.val (eval_varEqual_iff.mp this)

lemma eval_translate_iff {φ : Semiformula L₂ ξ n} {ε : ξ → π.Model M} {e : Fin n → π.Model M} :
    Evalm M (fun i ↦ e i) (fun i ↦ ε i) (π.translate φ) ↔ Evalm (π.Model M) e ε φ := by
  match φ with
  |  .rel R v => simp [eval_rel, eval_translateRel_iff]
  | .nrel R v => simp [eval_nrel, eval_translateRel_iff]
  |         ⊤ => simp
  |         ⊥ => simp
  |     φ ⋏ ψ => simp [eval_translate_iff (φ := φ), eval_translate_iff (φ := ψ)]
  |     φ ⋎ ψ => simp [eval_translate_iff (φ := φ), eval_translate_iff (φ := ψ)]
  |      ∀' φ =>
    suffices
      (∀ a : π.Model M, Evalm M (a :> fun i ↦ ↑(e i)) (fun i ↦ ↑(ε i)) (π.translate φ)) ↔
      (∀ a : π.Model M, Evalm (π.Model M) (a :> e) ε φ) by simpa
    exact forall_congr' fun a ↦ by simp [←eval_translate_iff (φ := φ), Matrix.comp_vecCons']
  |      ∃' φ =>
    suffices
      (∃ a : π.Model M, Evalm M (a :> fun i ↦ ↑(e i)) (fun i ↦ ↑(ε i)) (π.translate φ)) ↔
      (∃ a : π.Model M, Evalm (π.Model M) (a :> e) ε φ) by simpa
    exact exists_congr fun a ↦ by simp [←eval_translate_iff (φ := φ), Matrix.comp_vecCons']

@[simp] lemma eval_translate_iff₀ {σ : Sentence L₂} :
    M ⊧ₘ₀ π.translate σ ↔ π.Model M ⊧ₘ₀ σ := by
  simpa [models₀_iff, Matrix.empty_eq, Empty.eq_elim] using
    eval_translate_iff (M := M) (π := π) (ε := Empty.elim) (e := ![]) (φ := σ)

lemma models_translate_close₀_iff {φ : SyntacticFormula L₂} :
    M ⊧ₘ₀ π.translate (∀∀₀ φ) ↔ π.Model M ⊧ₘ φ := by
    simp only [eval_translate_iff₀]
    simp [models₀_iff, models_iff, eval_close₀]

end semantics

protected def id : Translation T₁ L₁ where
  domain := ⊤
  rel (r) := Semiformula.rel r (#·)
  func (f) := “z. z = !!(Semiterm.func f (#·.succ))”
  domain_nonempty := complete (T := T₁) <| EQ.provOf.{_,0} _ fun _ _ _ _ ↦ (by simp [models_iff])
  func_defined {k} (f) := complete (T := T₁) <| EQ.provOf.{_,0} _ fun _ _ _ _ _ ↦ by
    simp [models_iff, Semiterm.val_func]

end Translation

class Interpretation {L₁ L₂ : Language} [L₁.Eq] (T : Theory L₁) [𝐄𝐐 ⪯ T] (U : Theory L₂) where
  trl : Translation T L₂
  interpret_theory : ∀ φ ∈ U, T ⊢!. trl.translate (∀∀₀φ)

infix:50 " ⊳ " => Interpretation

namespace Interpretation

open Translation

variable {L₁ L₂ : Language} [L₁.Eq] {T : Theory L₁} [𝐄𝐐 ⪯ T] {U : Theory L₂} (π : T ⊳ U)

abbrev translate (φ : Semiformula L₂ ξ n) : Semiformula L₁ ξ n := π.trl.translate φ

lemma model_models_theory {M : Type v} [Nonempty M] [Structure L₁ M] [Structure.Eq L₁ M] (hT : M ⊧ₘ* T) :
    π.trl.Model M ⊧ₘ* U :=
  modelsTheory_iff.mpr fun {σ} hσ ↦
    models_translate_close₀_iff.mp (consequence_iff'.mp (sound! (T := T) (π.interpret_theory σ hσ)) M)

lemma of_provability {φ : SyntacticFormula L₂} (h : U ⊢! φ) : T ⊢!. π.translate (∀∀₀ φ) :=
  complete (T := T) <| EQ.provOf.{_,0} _ fun _ _ _ _ hT ↦
    models_translate_close₀_iff.mpr (models_of_provable (π.model_models_theory hT) h)

end Interpretation

end LO.FirstOrder

module

public import Foundation.FirstOrder.Completeness.Corollaries
public import Foundation.Vorspiel.ExistsUnique

@[expose] public section
/-!
# (Direct) Interpretation
-/

namespace LO.FirstOrder

@[ext]
structure DirectTranslation {L₁ : Language} [L₁.Eq] (T : Theory L₁) [𝗘𝗤 ⪯ T] (L₂ : Language) [L₂.Eq] where
  domain : Semisentence L₁ 1
  rel {k} : L₂.Rel k → Semisentence L₁ k
  func {k} : L₂.Func k → Semisentence L₁ (k + 1)
  domain_nonempty :
    T ⊢ ∃⁰ domain
  func_defined {k} (f : L₂.Func k) :
    T ⊢ ∀⁰* ((Matrix.conj fun i ↦ domain/[#i]) 🡒 ∃⁰! (domain/[#0] ⋏ func f))
  preserve_eq :
    T ⊢ “∀ x y, !domain x → !domain y → (!(rel Language.Eq.eq) x y ↔ x = y)”

namespace DirectTranslation

variable {L₁ L₂ : Language} [L₁.Eq] [L₂.Eq] {T : Theory L₁} [𝗘𝗤 ⪯ T]

variable (π : DirectTranslation T L₂)

def fal (φ : Semiformula L₁ ξ (n + 1)) : Semiformula L₁ ξ n := ∀⁰[Rew.emb ▹ π.domain/[#0]] φ

def exs (φ : Semiformula L₁ ξ (n + 1)) : Semiformula L₁ ξ n := ∃⁰[Rew.emb ▹ π.domain/[#0]] φ

notation:64 "∀_[" π "] " ψ => fal π ψ
notation:64 "∃_[" π "] " ψ => exs π ψ

@[simp] lemma neg_fal (φ : Semiformula L₁ ξ (n + 1)) : ∼(∀_[π] φ) = ∃_[π] ∼φ := by simp [fal, exs]

@[simp] lemma neg_exs (φ : Semiformula L₁ ξ (n + 1)) : ∼(∃_[π] φ) = ∀_[π] ∼φ := by simp [fal, exs]

def varEqual : Semiterm L₂ ξ n → Semiformula L₁ ξ (n + 1)
  |                     #x => “z. z = #x.succ”
  |                     &x => “z. z = &x”
  | .func (arity := k) f v =>
    ∀⁰^[k] (
      (Matrix.conj fun i ↦
        Rew.emb ▹ π.domain/[#(i.addCast (n + 1))] ⋏
        Rew.subst (#(i.addCast (n + 1)) :> fun j ↦ #((j.addNat 1).addNat k)) ▹ varEqual (v i))
      🡒 (Rew.embSubsts (#((0 : Fin (n + 1)).addNat k) :> fun i ↦ #(i.addCast (n + 1))) ▹ π.func f)
    )

def translateRel {k} (r : L₂.Rel k) (v : Fin k → Semiterm L₂ ξ n) : Semiformula L₁ ξ n :=
  ∀⁰^[k] (
    (Matrix.conj fun i ↦
      Rew.emb ▹ π.domain/[#(i.addCast n)] ⋏
      Rew.subst (#(i.addCast n) :> fun j ↦ #(j.addNat k)) ▹ π.varEqual (v i))
    🡒 (Rew.embSubsts (fun i ↦ #(i.addCast n)) ▹ π.rel r)
  )

def translateAux {n} : Semiformula L₂ ξ n → Semiformula L₁ ξ n
  | .rel r v  => π.translateRel r v
  | .nrel r v => ∼π.translateRel r v
  |         ⊤ => ⊤
  |         ⊥ => ⊥
  |     φ ⋏ ψ => translateAux φ ⋏ translateAux ψ
  |     φ ⋎ ψ => translateAux φ ⋎ translateAux ψ
  |      ∀⁰ φ => ∀_[π] translateAux φ
  |      ∃⁰ φ => ∃_[π] translateAux φ

lemma translateAux_neg {n : ℕ} (φ : Semiformula L₂ ξ n) : π.translateAux (∼φ) = ∼π.translateAux φ := by
  induction φ using Semiformula.rec' <;> simp [translateAux, *]

def translate : Semiformula L₂ ξ n →ˡᶜ Semiformula L₁ ξ n where
  toTr := π.translateAux
  map_top' := rfl
  map_bot' := rfl
  map_and' := fun _ _ ↦ rfl
  map_or' := fun _ _ ↦ rfl
  map_neg' := by simp [translateAux_neg]
  map_imply' := by simp [Semiformula.imp_eq, translateAux, translateAux_neg, ←Semiformula.neg_eq]

variable {π}

@[simp] lemma translate_rel {k} (R : L₂.Rel k) (v : Fin k → Semiterm L₂ ξ n) :
    π.translate (Semiformula.rel R v) = π.translateRel R v := rfl

@[simp] lemma translate_nrel {k} (R : L₂.Rel k) (v : Fin k → Semiterm L₂ ξ n) :
    π.translate (Semiformula.nrel R v) = ∼π.translateRel R v := rfl

@[simp] lemma translate_all (φ : Semiformula L₂ ξ (n + 1)) :
    π.translate (∀⁰ φ) = ∀_[π] π.translate φ := rfl

@[simp] lemma translate_ex (φ : Semiformula L₂ ξ (n + 1)) :
    π.translate (∃⁰ φ) = ∃_[π] π.translate φ := rfl

section semantics

open Semiformula

variable {M : Type*} [Structure L₁ M]

variable (π)

def Dom (x : M) : Prop := M ⊧/![x] π.domain

variable {π}

lemma dom_iff {x : M} : π.Dom x ↔ M ⊧/![x] π.domain := iff_of_eq rfl

lemma domain_exists [Nonempty M] [M ⊧ₘ* T] : ∃ x : M, π.Dom x := by
  simpa [models_iff] using models_of_provable (M := M) inferInstance π.domain_nonempty

variable (π M)

@[pp_using_anonymous_constructor, ext]
structure Model where
  val : M
  dom : π.Dom val

variable {π M}

attribute [coe] Model.val

instance : CoeOut (π.Model M) M := ⟨Model.val⟩

namespace Model

@[simp] lemma pval_sub_domain (x : π.Model M) : M ⊧/![x] π.domain := x.dom

instance [Nonempty M] [M ⊧ₘ* T] : Nonempty (π.Model M) := by
  rcases π.domain_exists (M := M) with ⟨x, hx⟩; exact ⟨⟨x, hx⟩⟩

@[simp] lemma coe_mem_domain (x : π.Model M) : π.Dom (x : M) := x.dom

@[simp] lemma val_mk (x : M) (hx : π.Dom x) : ↑(⟨x, hx⟩ : π.Model M) = x := rfl

@[simp] lemma eta (x : π.Model M) (h : π.Dom (x : M)) : (⟨(x : M), h⟩ : π.Model M) = x := rfl

@[simp] lemma val_inj_iff {x y : π.Model M} : x.val = y.val ↔ x = y :=
  ⟨fun h ↦ by ext; exact h, by rintro rfl; rfl⟩

@[simp] lemma val_mk_eq_iff {x y : M} {hx : π.Dom x} {hy : π.Dom y} :
    (⟨x, hx⟩ : π.Model M) = (⟨y, hy⟩ : π.Model M) ↔ x = y := by simp

@[simp] lemma eval_fal {φ : Semiformula L₁ ξ (n + 1)} :
    Evalm M e ε (∀_[π] φ) ↔ ∀ x : π.Model M, Evalm M (x :> e) ε φ := by
  suffices (∀ x, π.Dom x → Evalm M (x :> e) ε φ) ↔ ∀ x : π.Model M, (Evalm M (↑x :> e) ε) φ by
    simpa [fal, ←dom_iff, Matrix.constant_eq_singleton]
  constructor
  · intro h x; exact h x x.dom
  · intro h x hx; simpa using h ⟨x, hx⟩

@[simp] lemma eval_exs {φ : Semiformula L₁ ξ (n + 1)} :
    Evalm M e ε (∃_[π] φ) ↔ ∃ x : π.Model M, Evalm M (x :> e) ε φ := by
  suffices (∃ x, π.Dom x ∧ Evalm M (x :> e) ε φ) ↔ ∃ x : π.Model M, (Evalm M (↑x :> e) ε) φ by
    simpa [exs, ←dom_iff, Matrix.constant_eq_singleton]
  constructor
  · rintro ⟨x, hx, H⟩; exact ⟨⟨x, hx⟩, by simpa using H⟩
  · rintro ⟨x, H⟩; exact ⟨x, by simp, H⟩

variable [Nonempty M] [M ⊧ₘ* T] [Structure.Eq L₁ M]

lemma func_existsUnique_on_dom {k} (f : L₂.Func k) :
    ∀ (v : Fin k → M), (∀ i, π.Dom (v i)) → ∃! y, π.Dom y ∧ Evalbm M (y :> v) (π.func f) := by
  simpa [Dom, models_iff, eval_substs, Matrix.constant_eq_singleton] using
    models_of_provable (M := M) inferInstance (π.func_defined f)

lemma func_existsUnique {k} (f : L₂.Func k) (v : Fin k → π.Model M) :
    ∃! y : π.Model M, M ⊧/(y :> fun i ↦ v i) (π.func f) := by
  have : ∃! y, π.Dom y ∧ M ⊧/(y :> fun i ↦ v i) (π.func f) :=
    func_existsUnique_on_dom (π := π) f (fun i ↦ (v i : M)) (fun i ↦ by simp)
  rcases this.exists with ⟨y, hy, Hy⟩
  exact ExistsUnique.intro ⟨y, hy⟩ (by simpa using Hy)
    fun z Hz ↦ by
      rcases show y = ↑z from this.unique ⟨hy, Hy⟩ ⟨z.dom, Hz⟩
      simp

variable (π M)

noncomputable instance struc : Structure L₂ (π.Model M) where
  rel _ R v := Semiformula.Evalbm M (fun i ↦ (v i)) (π.rel R)
  func _ f v := Classical.choose! (func_existsUnique (π := π) f v)

variable {π M}

lemma rel_iff {k} (r : L₂.Rel k) (v : Fin k → π.Model M) :
    Structure.rel r v ↔ Semiformula.Evalbm M (fun i ↦ (v i)) (π.rel r) := iff_of_eq rfl

@[simp] lemma eq_iff' {a b : π.Model M} :
    M ⊧/![a, b] (π.rel Language.Eq.eq) ↔ a = b := by
  have : ∀ x y, π.Dom x → π.Dom y → (M ⊧/![x, y] (π.rel Language.Eq.eq) ↔ x = y) := by
    simpa [models_iff, Matrix.comp_vecCons', Matrix.constant_eq_singleton, ←dom_iff]
      using models_of_provable (inferInstanceAs (M ⊧ₘ* T)) π.preserve_eq
  simpa using this a b

@[simp] lemma eq_iff (v : Fin 2 → π.Model M) :
    Structure.rel (Language.Eq.eq : L₂.Rel 2) v ↔ v 0 = v 1 := by
  simp [Model.rel_iff]
  simp [Matrix.fun_eq_vec_two (v := fun i ↦ (v i : M))]

instance : Structure.Eq L₂ (π.Model M) where
  eq a b := by simp [Operator.val, Operator.Eq.sentence_eq, eval_rel]

lemma func_iff {k} {f : L₂.Func k} {y : π.Model M} {v : Fin k → π.Model M} :
    y = Structure.func f v ↔ Evalbm M (y :> fun i ↦ v i) (π.func f) := Classical.choose!_eq_iff_right _

lemma func_iff' {k} {f : L₂.Func k} {y : M} {v : Fin k → π.Model M} :
    y = Structure.func f v ↔ π.Dom y ∧ Evalbm M (y :> fun i ↦ v i) (π.func f) := by
  constructor
  · rintro rfl; simp [←func_iff]
  · intro h
    exact (func_existsUnique_on_dom f (fun i ↦ (v i : M)) (by simp)).unique h (by simp [←func_iff])

@[simp] lemma eval_func {k} (f : L₂.Func k) (v : Fin k → π.Model M) :
    Evalbm M (↑(Structure.func f v) :> fun i ↦ v i) (π.func f) := by simp [←func_iff]

lemma eval_varEqual_iff {t : Semiterm L₂ ξ n} {ε : ξ → π.Model M} {y : π.Model M} {x : Fin n → π.Model M} :
    Evalm M (y :> fun i ↦ x i) (fun x ↦ ε x) (π.varEqual t) ↔ y = t.valm (π.Model M) x ε := by
  match t with
  |                     #_ => simp [varEqual]
  |                     &_ => simp [varEqual]
  | .func (arity := k) f v =>
    suffices
      (∀ w : Fin k → M,
        (∀ i, π.Dom (w i) ∧ Evalm M (w i :> fun i ↦ x i) (fun x ↦ ε x) (π.varEqual (v i))) →
          M ⊧/(y :> w) (π.func f)) ↔
      M ⊧/(y :> fun i ↦ (v i).valm (π.Model M) x ε) (π.func f) by
        simpa [varEqual, eval_embSubsts, Matrix.comp_vecCons', Matrix.constant_eq_singleton,
          Semiterm.val_func, func_iff, ←dom_iff]
    constructor
    · intro h; apply h
      intro i
      simp [eval_varEqual_iff (t := v i)]
    · intro h w hw
      suffices w = fun i ↦ ↑((v i).valm (π.Model M) x ε) by rcases this; exact h
      ext i
      let w' : π.Model M := ⟨w i, (hw i).1⟩
      have : Evalm M (w' :> fun i ↦ x i) (fun x ↦ ε x) (π.varEqual (v i)) := by simp [w', hw]
      simpa [w'] using congr_arg Model.val (eval_varEqual_iff.mp this)

lemma eval_translateRel_iff {n k} {ε : ξ → π.Model M} (e : Fin n → π.Model M) (R : L₂.Rel k) (v : Fin k → Semiterm L₂ ξ n) :
    Evalm M (fun i ↦ e i) (fun i ↦ ε i) (π.translateRel R v) ↔ Structure.rel R fun i ↦ Semiterm.valm (π.Model M) e ε (v i) := by
  suffices
    (∀ w, (∀ i, π.Dom (w i) ∧ (Evalm M (w i :> fun i ↦ ↑(e i)) fun i ↦ ↑(ε i)) (π.varEqual (v i))) → M ⊧/w (π.rel R)) ↔
    M ⊧/(fun i ↦ ↑((v i).valm (π.Model M) e ε)) (π.rel R) by
      simpa [translateRel, Matrix.comp_vecCons', rel_iff, eval_embSubsts, Matrix.constant_eq_singleton, ←dom_iff]
  constructor
  · intro h
    exact h (fun i ↦ ↑((v i).valm (π.Model M) e ε)) (fun i ↦ by simp [eval_varEqual_iff])
  · intro h w hw
    suffices w = fun i ↦ ↑((v i).valm (π.Model M) e ε) by rcases this; exact h
    ext i
    let w' : π.Model M := ⟨w i, (hw i).1⟩
    have : Evalm M (w' :> fun i ↦ e i) (fun x ↦ ε x) (π.varEqual (v i)) := by simp [w', hw]
    simpa [w'] using congr_arg Model.val (eval_varEqual_iff.mp this)

lemma eval_translate_iff {φ : Semiformula L₂ ξ n} {ε : ξ → π.Model M} {e : Fin n → π.Model M} :
    Evalm M (fun i ↦ e i) (fun i ↦ ε i) (π.translate φ) ↔ Evalm (π.Model M) e ε φ := by
  match φ with
  |  .rel R v => simp [eval_rel, eval_translateRel_iff]
  | .nrel R v => simp [eval_nrel, eval_translateRel_iff]
  |         ⊤ => simp
  |         ⊥ => simp
  |     φ ⋏ ψ => simp [eval_translate_iff (φ := φ), eval_translate_iff (φ := ψ)]
  |     φ ⋎ ψ => simp [eval_translate_iff (φ := φ), eval_translate_iff (φ := ψ)]
  |      ∀⁰ φ =>
    suffices
      (∀ a : π.Model M, Evalm M (a :> fun i ↦ ↑(e i)) (fun i ↦ ↑(ε i)) (π.translate φ)) ↔
      (∀ a : π.Model M, Evalm (π.Model M) (a :> e) ε φ) by simpa
    exact forall_congr' fun a ↦ by simp [←eval_translate_iff (φ := φ), Matrix.comp_vecCons']
  |      ∃⁰ φ =>
    suffices
      (∃ a : π.Model M, Evalm M (a :> fun i ↦ ↑(e i)) (fun i ↦ ↑(ε i)) (π.translate φ)) ↔
      (∃ a : π.Model M, Evalm (π.Model M) (a :> e) ε φ) by simpa
    exact exists_congr fun a ↦ by simp [←eval_translate_iff (φ := φ), Matrix.comp_vecCons']

lemma evalb_translate_iff {φ : Semisentence L₂ n} {e : Fin n → π.Model M} :
    M ⊧/(fun i ↦ e i) (π.translate φ) ↔ (π.Model M) ⊧/e φ := by simp [←eval_translate_iff, Empty.eq_elim]

lemma evalb_cons_translate_iff {φ : Semisentence L₂ (n + 1)} {x : π.Model M} {e : Fin n → π.Model M} :
    M ⊧/(x :> fun i ↦ e i) (π.translate φ) ↔ (π.Model M) ⊧/(x :> e) φ := by
  simp [←eval_translate_iff, Empty.eq_elim, Matrix.comp_vecCons']

lemma evalb_singleton_translate_iff {φ : Semisentence L₂ 1} {x : π.Model M} :
    M ⊧/![x] (π.translate φ) ↔ (π.Model M) ⊧/![x] φ := by
  simp [←eval_translate_iff, Empty.eq_elim, Matrix.constant_eq_singleton]

lemma evalb_doubleton_translate_iff {φ : Semisentence L₂ 2} {x y : π.Model M} :
    M ⊧/![x, y] (π.translate φ) ↔ (π.Model M) ⊧/![x, y] φ := by
  simp [←eval_translate_iff, Empty.eq_elim, Matrix.constant_eq_singleton, Matrix.comp_vecCons']

lemma translate_iff {σ : Sentence L₂} :
    M ⊧ₘ π.translate σ ↔ π.Model M ⊧ₘ σ := by
  simpa [models_iff, Matrix.empty_eq, Empty.eq_elim] using
    eval_translate_iff (M := M) (π := π) (ε := Empty.elim) (e := ![]) (φ := σ)

end Model

end semantics

variable (T)

protected def id : DirectTranslation T L₁ where
  domain := ⊤
  rel R := Semiformula.rel R (#·)
  func f := “z. z = !!(Semiterm.func f (#·.succ))”
  domain_nonempty := complete <| EQ.provOf.{_,0} _ fun _ _ _ _ ↦ (by simp [models_iff])
  func_defined {k} f := complete <| EQ.provOf.{_,0} _ fun _ _ _ _ _ ↦ by
    simp [models_iff, Semiterm.val_func]
  preserve_eq := complete <| EQ.provOf.{_,0} _ fun M _ _ _ _ ↦ by
    simp [models_iff, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Semiformula.eval_rel]

lemma id_func_def : (DirectTranslation.id T).func f = “z. z = !!(Semiterm.func f (#·.succ))” := rfl

lemma id_rel_def : (DirectTranslation.id T).rel R = Semiformula.rel R (#·) := rfl

variable {T}

section semantics

open DirectTranslation Semiformula

variable {M : Type*} [Structure L₁ M]

@[simp] lemma id_Dom (x : M) : (DirectTranslation.id T).Dom x := by simp [dom_iff, DirectTranslation.id]

variable [Nonempty M] [M ⊧ₘ* T] [Structure.Eq L₁ M]

@[simp] lemma id_val_eq
    {ε : ξ → (DirectTranslation.id T).Model M} {e : Fin n → (DirectTranslation.id T).Model M} {t : Semiterm L₁ ξ n} :
    t.valm ((DirectTranslation.id T).Model M) e ε = t.valm M (fun x ↦ e x) (fun x ↦ ε x) := by
  match t with
  |        #x => simp
  |        &x => simp
  | .func f v =>
    have : ∀ i, (v i).valm ((DirectTranslation.id T).Model M) e ε = (v i).valm M (fun x ↦ e x) (fun x ↦ ε x) := fun i ↦
      id_val_eq (t := v i) (e := e) (ε := ε)
    symm
    simp [Semiterm.val_func, Model.func_iff',
      id_func_def, Semiterm.val_func, this]

@[simp] lemma id_models_iff
    {ε : ξ → (DirectTranslation.id T).Model M} {e : Fin n → (DirectTranslation.id T).Model M} {φ : Semiformula L₁ ξ n} :
    Evalm ((DirectTranslation.id T).Model M) e ε φ ↔ Evalm M (fun x ↦ e x) (fun x ↦ ε x) φ := by
  match φ with
  |  .rel R v => simp [eval_rel, Model.rel_iff, id_rel_def]
  | .nrel R v => simp [eval_nrel, eval_rel, Model.rel_iff, id_rel_def]
  |         ⊤ => simp
  |         ⊥ => simp
  |     φ ⋏ ψ => simp [id_models_iff (φ := φ), id_models_iff (φ := ψ)]
  |     φ ⋎ ψ => simp [id_models_iff (φ := φ), id_models_iff (φ := ψ)]
  |      ∀⁰ φ =>
    simp only [eval_all, Nat.succ_eq_add_one, id_models_iff (φ := φ), Matrix.comp_vecCons']
    constructor
    · intro h x; simpa using h ⟨x, by simp⟩
    · rintro h x; simpa using h x
  |      ∃⁰ φ =>
    simp only [eval_ex, Nat.succ_eq_add_one, id_models_iff (φ := φ), Matrix.comp_vecCons']
    constructor
    · rintro ⟨x, h⟩; exact ⟨x, h⟩
    · rintro ⟨x, h⟩; exact ⟨⟨x, by simp⟩, by simpa using h⟩

end semantics

end DirectTranslation

class DirectInterpretation {L₁ L₂ : Language} [L₁.Eq] [L₂.Eq] (T : Theory L₁) [𝗘𝗤 ⪯ T] (U : Theory L₂) where
  trln : DirectTranslation T L₂
  interpret_theory : ∀ φ ∈ U, T ⊢ trln.translate φ

infix:50 " ⊳ " => DirectInterpretation

abbrev InterpretedBy {L₁ L₂ : Language} [L₁.Eq] [L₂.Eq] (U : Theory L₂) (T : Theory L₁) [𝗘𝗤 ⪯ T] := T ⊳ U

infix:50 " ⊲ " => InterpretedBy

class MutualDirectInterpretation {L₁ L₂ : Language} [L₁.Eq] [L₂.Eq] (T : Theory L₁) [𝗘𝗤 ⪯ T] (U : Theory L₂) [𝗘𝗤 ⪯ U] where
  r : T ⊳ U
  l : T ⊲ U

infix:50 " ⋈ " => MutualDirectInterpretation

namespace DirectInterpretation

open DirectTranslation

section

variable {L₁ L₂ : Language} [L₁.Eq] [L₂.Eq] {T : Theory L₁} [𝗘𝗤 ⪯ T] {U : Theory L₂} (π : T ⊳ U)

abbrev translate (φ : Semiformula L₂ ξ n) : Semiformula L₁ ξ n := π.trln.translate φ

abbrev Model (M : Type*) [Structure L₁ M] : Type _ := π.trln.Model M

open Classical in
instance model_models_theory {M : Type v} [Nonempty M] [Structure L₁ M] [Structure.Eq L₁ M] (hT : M ⊧ₘ* T) :
    π.Model M ⊧ₘ* U :=
  modelsTheory_iff.mpr fun {σ} hσ ↦
    Model.translate_iff.mp <| consequence_iff'.mp (sound! (π.interpret_theory σ hσ)) M

open Classical in
lemma of_provability {σ : Sentence L₂} (h : U ⊢ σ) : T ⊢ π.translate σ :=
  complete <| EQ.provOf.{_,0} _ fun _ _ _ _ hT ↦
    Model.translate_iff.mpr <| models_of_provable (π.model_models_theory hT) h

end

def ofWeakerThan {L : Language} [L.Eq] (T U : Theory L) [𝗘𝗤 ⪯ T] [U ⪯ T] : U ⊲ T where
  trln := DirectTranslation.id T
  interpret_theory φ hφ := complete <| EQ.provOf.{_,0} _ fun M _ _ _ hT ↦
    Model.translate_iff.mpr <| by
      suffices M ⊧/ ![] φ by simpa [models_iff, Empty.eq_elim, Matrix.empty_eq]
      have : T ⊢ φ := Entailment.weakerThan_iff.mp (inferInstanceAs (U ⪯ T)) (Entailment.by_axm _ (by simp [hφ]))
      exact models_of_provable hT this

protected instance refl {L : Language} [L.Eq] (T : Theory L) [𝗘𝗤 ⪯ T] : T ⊳ T := ofWeakerThan T T

section composition

variable {L₁ L₂ L₃ : Language} [L₁.Eq] [L₂.Eq] [L₃.Eq] {T₁ : Theory L₁} {T₂ : Theory L₂} {T₃ : Theory L₃} [𝗘𝗤 ⪯ T₁] [𝗘𝗤 ⪯ T₂] [𝗘𝗤 ⪯ T₃]

def compDirectTranslation (τ : DirectTranslation T₂ L₃) (π : T₁ ⊳ T₂) : DirectTranslation T₁ L₃ where
  domain := π.trln.domain ⋏ π.translate τ.domain
  domain_nonempty := by simpa [exs] using π.of_provability τ.domain_nonempty
  rel R := π.translate (τ.rel R)
  func {k} f := π.translate (τ.func f)
  func_defined {k} f := complete <| EQ.provOf.{_,0} _ fun M _ _ _ hT ↦ by
    apply models_iff.mpr
    suffices
      ∀ w,
      (∀ i, π.trln.Dom (w i) ∧ M ⊧/![w i] (π.translate τ.domain)) →
        ∃! x,
          (π.trln.Dom x ∧ M ⊧/![x] (π.translate τ.domain)) ∧
            M ⊧/(x :> w) (π.translate (τ.func f)) by
      simpa [Matrix.constant_eq_singleton, Model.eval_translate_iff, ←dom_iff]
    intro w hw
    have iT₂ : π.Model M ⊧ₘ* T₂ := π.model_models_theory hT
    let w' : Fin k → τ.Model (π.Model M) :=
      fun i ↦ ⟨⟨w i, (hw i).1⟩, Model.evalb_translate_iff.mp <| by simpa [Matrix.constant_eq_singleton] using (hw i).2⟩
    let y := (Structure.func f w')
    apply ExistsUnique.intro ↑↑(Structure.func f w')
    · rw [show w = (fun i ↦ ↑↑(w' i)) by ext i; simp [w']]
      simp [Model.evalb_cons_translate_iff, Model.evalb_singleton_translate_iff]
    · rintro y ⟨⟨hy, hhy⟩, hf⟩
      let y' : τ.Model (π.Model M) := ⟨⟨y, hy⟩, Model.evalb_translate_iff.mp <| by simpa [Matrix.constant_eq_singleton] using hhy⟩
      suffices y' = Structure.func f w' by simpa [y'] using congr_arg Model.val <| congr_arg Model.val this
      apply Model.func_iff.mpr <| Model.evalb_cons_translate_iff.mp <| by simpa [y', w'] using hf
  preserve_eq := complete <| EQ.provOf.{_,0} _ fun M _ _ _ hT ↦ by
    apply models_iff.mpr
    have : π.Model M ⊧ₘ* T₂ := π.model_models_theory hT
    suffices
      ∀ (x y : M),
        π.trln.Dom x → M ⊧/![x] (π.translate τ.domain) →
        π.trln.Dom y → M ⊧/![y] (π.translate τ.domain) →
          (M ⊧/![x, y] (π.translate (τ.rel Language.Eq.eq)) ↔ x = y) by
      simpa [Matrix.comp_vecCons', Matrix.constant_eq_singleton, Model.eval_translate_iff, ←dom_iff]
    intro x y hx hhx hy hhy
    let x' : τ.Model (π.Model M) := ⟨⟨x, hx⟩, by simpa [dom_iff, ←Model.evalb_singleton_translate_iff] using hhx⟩
    let y' : τ.Model (π.Model M) := ⟨⟨y, hy⟩, by simpa [dom_iff, ←Model.evalb_singleton_translate_iff] using hhy⟩
    rw [show x = ↑↑x' by simp [x'], show y = ↑↑y' by simp [y']]
    simp [Model.evalb_doubleton_translate_iff]

@[simp] lemma compDirectTranslation_domain_def (τ : DirectTranslation T₂ L₃) (π : T₁ ⊳ T₂) :
    (compDirectTranslation τ π).domain = π.trln.domain ⋏ π.translate τ.domain := rfl

@[simp] lemma compDirectTranslation_func_def (τ : DirectTranslation T₂ L₃) (π : T₁ ⊳ T₂) (f : L₃.Func k) :
    (compDirectTranslation τ π).func f = π.translate (τ.func f) := rfl

@[simp] lemma compDirectTranslation_rel_def (τ : DirectTranslation T₂ L₃) (π : T₁ ⊳ T₂) (R : L₃.Rel k) :
    (compDirectTranslation τ π).rel R = π.translate (τ.rel R) := rfl

section semantics

open Semiformula

variable (τ : DirectTranslation T₂ L₃) (π : T₁ ⊳ T₂)
    {M : Type*} [Nonempty M] [Structure L₁ M] [Structure.Eq L₁ M] [M ⊧ₘ* T₁]

lemma compDirectTranslation_Dom_iff {x : M} : (compDirectTranslation τ π).Dom x ↔ (∃ z : τ.Model (π.Model M), x = z) := by
  suffices π.trln.Dom x ∧ M ⊧/![x] (π.translate τ.domain) ↔ ∃ z : τ.Model (π.Model M), x = ↑↑z by
    simpa [dom_iff (π := compDirectTranslation τ π), ←dom_iff (π := π.trln)]
  constructor
  · rintro ⟨hx, H⟩
    exact ⟨⟨⟨x, hx⟩, by simpa [dom_iff, ←Model.evalb_singleton_translate_iff] using H⟩, by simp⟩
  · rintro ⟨z, rfl, hz⟩; simp [Model.evalb_singleton_translate_iff]

lemma val_compDirectTranslation_Model_equiv {t : Semiterm L₃ ξ n}
    {ε : ξ → (compDirectTranslation τ π).Model M} {ε' : ξ → τ.Model (π.Model M)} (hε : ∀ x, (ε x : M) = ε' x)
    {e : Fin n → (compDirectTranslation τ π).Model M} {e' : Fin n → τ.Model (π.Model M)} (he : ∀ x, (e x : M) = e' x) :
    (t.valm ((compDirectTranslation τ π).Model M) e ε : M) = t.valm (τ.Model (π.Model M)) e' ε' := by
  match t with
  |        #x => simp [he]
  |        &x => simp [hε]
  | .func f v =>
    have ih : ∀ i, ((v i).valm ((compDirectTranslation τ π).Model M) e ε : M) = (v i).valm (τ.Model (π.Model M)) e' ε' :=
      fun i ↦ val_compDirectTranslation_Model_equiv hε he
    suffices
      (↑(Structure.func f fun i ↦ (v i).val (Model.struc τ (π.Model M)) e' ε') : M) =
      (Structure.func f fun i ↦ Semiterm.val (Model.struc (compDirectTranslation τ π) M) e ε (v i)) by symm; simpa [Semiterm.val_func]
    apply Model.func_iff'.mpr
    simp [compDirectTranslation_Dom_iff, Model.evalb_cons_translate_iff, ih]

lemma eval_compDirectTranslation_Model_equiv {φ : Semiformula L₃ ξ n}
    {ε : ξ → (compDirectTranslation τ π).Model M} {ε' : ξ → τ.Model (π.Model M)} (hε : ∀ x, (ε x : M) = ε' x)
    {e : Fin n → (compDirectTranslation τ π).Model M} {e' : Fin n → τ.Model (π.Model M)} (he : ∀ x, (e x : M) = e' x) :
    Semiformula.Evalm ((compDirectTranslation τ π).Model M) e ε φ ↔ Semiformula.Evalm (τ.Model (π.Model M)) e' ε' φ := by
  match φ with
  | .rel R v =>
    have ih : ∀ i, ((v i).valm ((compDirectTranslation τ π).Model M) e ε : M) = (v i).valm (τ.Model (π.Model M)) e' ε' :=
      fun i ↦ val_compDirectTranslation_Model_equiv τ π hε he
    simp [eval_rel, Model.rel_iff, Model.evalb_translate_iff, ih]
  | .nrel R v =>
    have ih : ∀ i, ((v i).valm ((compDirectTranslation τ π).Model M) e ε : M) = (v i).valm (τ.Model (π.Model M)) e' ε' :=
      fun i ↦ val_compDirectTranslation_Model_equiv τ π hε he
    simp [eval_nrel, Model.rel_iff, Model.evalb_translate_iff, ih]
  | ⊤ => simp
  | ⊥ => simp
  | φ ⋏ ψ => simp [eval_compDirectTranslation_Model_equiv (φ := φ) hε he, eval_compDirectTranslation_Model_equiv (φ := ψ) hε he]
  | φ ⋎ ψ => simp [eval_compDirectTranslation_Model_equiv (φ := φ) hε he, eval_compDirectTranslation_Model_equiv (φ := ψ) hε he]
  | ∀⁰ φ =>
    simp only [eval_all, Nat.succ_eq_add_one]
    constructor
    · intro h x
      apply (eval_compDirectTranslation_Model_equiv hε ?_).mp <| h ⟨x, by simp [compDirectTranslation_Dom_iff]⟩
      intro i; cases i using Fin.cases <;> simp [he]
    · intro h x
      rcases (compDirectTranslation_Dom_iff τ π).mp x.dom with ⟨z, hz⟩
      apply (eval_compDirectTranslation_Model_equiv hε ?_).mpr (h z)
      · intro i; cases i using Fin.cases <;> simp [he, hz]
  | ∃⁰ φ =>
    simp only [eval_ex, Nat.succ_eq_add_one]
    constructor
    · rintro ⟨x, hx⟩
      rcases (compDirectTranslation_Dom_iff τ π).mp x.dom with ⟨z, hz⟩
      refine ⟨z, ?_⟩
      apply (eval_compDirectTranslation_Model_equiv hε ?_).mp hx
      intro i; cases i using Fin.cases <;> simp [he, hz]
    · rintro ⟨x, hx⟩
      refine ⟨⟨x, by simp [compDirectTranslation_Dom_iff]⟩, ?_⟩
      apply (eval_compDirectTranslation_Model_equiv hε ?_).mpr hx
      intro i; cases i using Fin.cases <;> simp [he]

instance compDirectTranslation_Model_equiv :
    (compDirectTranslation τ π).Model M ≡ₑ[L₃] τ.Model (π.Model M) := .mk <| fun {φ} ↦ by
  simp only [models_iff]
  constructor
  · intro h
    apply (eval_compDirectTranslation_Model_equiv τ π (by simp) (by simp)).mp h
  · intro h
    exact (eval_compDirectTranslation_Model_equiv τ π (by simp) (by simp)).mpr h

end semantics

protected def comp (τ : T₂ ⊳ T₃) (π : T₁ ⊳ T₂) : T₁ ⊳ T₃ where
  trln := compDirectTranslation τ.trln π
  interpret_theory φ hφ := complete <| EQ.provOf.{_,0} _ fun M _ _ _ hT ↦ by
    apply models_iff.mpr
    suffices τ.Model (π.Model M) ⊧ₘ φ by
      apply Model.translate_iff.mpr <| (compDirectTranslation_Model_equiv τ.trln π).models.mpr this
    have : τ.Model (π.Model M) ⊧ₘ* T₃ := inferInstance
    exact modelsTheory_iff.mp this hφ

end composition

end DirectInterpretation

namespace MutualDirectInterpretation

variable {L₁ L₂ L₃ : Language} [L₁.Eq] [L₂.Eq] [L₃.Eq] {T₁ : Theory L₁} {T₂ : Theory L₂} {T₃ : Theory L₃} [𝗘𝗤 ⪯ T₁] [𝗘𝗤 ⪯ T₂] [𝗘𝗤 ⪯ T₃]

protected instance refl (T : Theory L₁) [𝗘𝗤 ⪯ T] : T ⋈ T := ⟨DirectInterpretation.refl T, DirectInterpretation.refl T⟩

protected def symm (π : T₁ ⋈ T₂) : T₂ ⋈ T₁ := ⟨π.l, π.r⟩

protected def trans (π : T₁ ⋈ T₂) (τ : T₂ ⋈ T₃) : T₁ ⋈ T₃ := ⟨τ.r.comp π.r, π.l.comp τ.l⟩

end MutualDirectInterpretation

end LO.FirstOrder

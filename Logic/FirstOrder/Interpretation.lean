import Logic.FirstOrder.Basic
import Logic.FirstOrder.Completeness.Completeness
import Logic.FirstOrder.Completeness.Lemmata
import Logic.Vorspiel.ExistsUnique

namespace LO.FirstOrder

@[ext]
structure Interpretation {L : Language} [L.Eq] (T : Theory L) (L' : Language) where
  domain : Semisentence L 1
  rel {k} : L'.Rel k → Semisentence L k
  func {k} : L'.Func k → Semisentence L (k + 1)
  domain_nonempty :
    T ⊨₌ ∃' domain
  func_defined {k} (f : L'.Func k) :
    T ⊨₌ ∀* ((Matrix.conj fun i ↦ domain/[#i]) ⟶ ∃'! (domain/[#0] ⋏ func f))

namespace Interpretation

variable {L L' : Language.{u}} [L.Eq] {T : Theory L}

variable (ι : Interpretation T L')

def varEquals {n : ℕ} : Semiterm L' Empty n → Semisentence L (n + 1)
  | #x                => “#0 = !!#x.succ”
  | Semiterm.func f v =>
      Rew.toS.hom
        <| ∀* ((Matrix.conj fun i ↦ (Rew.embSubsts ![#i]).hom ι.domain ⋏ (Rew.embSubsts (#i :> (& ·.succ))).hom (varEquals <| v i)) ⟶
          (Rew.embSubsts (&0 :> (# ·))).hom (ι.func f))

def translationRel {k} (r : L'.Rel k) (v : Fin k → Semiterm L' Empty n) : Semisentence L n :=
  Rew.toS.hom <| ∀* ((Matrix.conj fun i ↦ (Rew.embSubsts ![#i]).hom ι.domain ⋏ (Rew.embSubsts (#i :> (& ·))).hom (ι.varEquals <| v i)) ⟶ Rew.emb.hom (ι.rel r))

def translationAux : {n : ℕ} → Semisentence L' n → Semisentence L n
  | _, Semiformula.rel r v  => ι.translationRel r v
  | _, Semiformula.nrel r v => ~ι.translationRel r v
  | _, ⊤                    => ⊤
  | _, ⊥                    => ⊥
  | _, p ⋏ q                => translationAux p ⋏ translationAux q
  | _, p ⋎ q                => translationAux p ⋎ translationAux q
  | _, ∀' p                 => ∀[ι.domain/[#0]] translationAux p
  | _, ∃' p                 => ∃[ι.domain/[#0]] translationAux p

lemma translationAux_neg {n : ℕ} (p : Semisentence L' n) : ι.translationAux (~p) = ~ ι.translationAux p := by
  induction p using Semiformula.rec' <;> simp [translationAux, *, ←Semiformula.neg_eq]

def translation {n : ℕ} : Semisentence L' n →ˡᶜ Semisentence L n where
  toTr := ι.translationAux
  map_top' := rfl
  map_bot' := rfl
  map_and' := fun _ _ ↦ rfl
  map_or' := fun _ _ ↦ rfl
  map_neg' := by simp [translationAux_neg]
  map_imply' := by simp [Semiformula.imp_eq, translationAux, translationAux_neg, ←Semiformula.neg_eq]

@[simp] lemma translation_rel {k} (r : L'.Rel k) (v : Fin k → Semiterm L' Empty n) :
    ι.translation (Semiformula.rel r v) = ι.translationRel r v := rfl

@[simp] lemma translation_nrel {k} (r : L'.Rel k) (v : Fin k → Semiterm L' Empty n) :
    ι.translation (Semiformula.nrel r v) = ~ι.translationRel r v := rfl

@[simp] lemma translation_all (p : Semisentence L' (n + 1)) : ι.translation (∀' p) = ∀[ι.domain/[#0]] ι.translation p := rfl

@[simp] lemma translation_ex (p : Semisentence L' (n + 1)) : ι.translation (∃' p) = ∃[ι.domain/[#0]] ι.translation p := rfl

section semantics

open Semiformula

variable {M : Type u} [Nonempty M] [s : Structure L M] [Structure.Eq L M] [M ⊧ₘ* T]

def Dom (x : M) : Prop := Evalbm M ![x] ι.domain

variable (M)

lemma dom_iff {x : M} : ι.Dom x ↔ Evalbm M ![x] ι.domain := iff_of_eq rfl

abbrev Sub := {x : M // ι.Dom x}

@[simp] lemma pval_sub_domain (x : ι.Sub M) : Evalbm M ![x] ι.domain := x.prop

lemma sub_exists : ∃ x : M, ι.Dom x := by
  simpa [Dom, models_iff, eval_substs, Matrix.constant_eq_singleton] using consequence_iff_add_eq.mp ι.domain_nonempty M inferInstance

lemma func_existsUnique_on_dom {k} (f : L'.Func k) : ∀ (v : Fin k → M), (∀ i, ι.Dom (v i)) → ∃! y, ι.Dom y ∧ Evalbm M (y :> v) (ι.func f) := by
  simpa [Dom, models_iff, eval_substs, Matrix.constant_eq_singleton] using consequence_iff_add_eq.mp (ι.func_defined f) M inferInstance

lemma func_existsUnique {k} (f : L'.Func k) (v : Fin k → ι.Sub M) : ∃! y : ι.Sub M, Evalbm M (y :> fun i ↦ v i) (ι.func f) := by
  have : ∃! y, ι.Dom y ∧ Evalbm M (y :> fun i ↦ v i) (ι.func f) := ι.func_existsUnique_on_dom M f (fun i ↦ v i) (fun i ↦ by simp [(v i).prop])
  rcases this.exists with ⟨y, hy, Hy⟩
  exact ExistsUnique.intro ⟨y, hy⟩ (by simpa using Hy) (by simp; intro z hz Hz; exact this.unique ⟨hz, Hz⟩ ⟨hy, Hy⟩)

variable {ι M}

instance sub_nonempty : Nonempty (ι.Sub M) := by simpa using ι.sub_exists M

noncomputable instance subStructure : Structure L' (ι.Sub M) where
  rel _ r v := Semiformula.Evalbm M (fun i ↦ (v i)) (ι.rel r)
  func _ f v := Classical.choose! (ι.func_existsUnique M f v)

lemma sub_rel_iff {k} (r : L'.Rel k) (v : Fin k → ι.Sub M) :
    Structure.rel r v ↔ Semiformula.Evalbm M (fun i ↦ (v i)) (ι.rel r) := iff_of_eq rfl

lemma sub_func_iff {k} (f : L'.Func k) (y : ι.Sub M) (v : Fin k → ι.Sub M) :
    y = Structure.func f v ↔ Evalbm M (y :> fun i ↦ v i) (ι.func f) := Classical.choose!_eq_iff _

lemma eval_varEquals_iff {t : Semiterm L' Empty n} {y : ι.Sub M} {x : Fin n → ι.Sub M} :
    Evalbm M (y :> fun i ↦ x i) (ι.varEquals t) ↔ y = Semiterm.valbm (ι.Sub M) x t := by
  induction t generalizing x y
  case bvar => simp [varEquals, Subtype.coe_inj]
  case fvar => contradiction
  case func k f w ih =>
    simp [varEquals, eval_embSubsts, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Semiterm.val_func, sub_func_iff]
    constructor
    · intro h; exact h _ (fun i ↦ ⟨ι.pval_sub_domain M _, (@ih i (Semiterm.valbm (Sub ι M) x (w i)) x).mpr rfl⟩)
    · rintro h v hv
      have : v = fun i ↦ (Semiterm.valbm (Sub ι M) x (w i)).val :=
        funext fun i ↦ by simpa using congr_arg Subtype.val ((@ih i ⟨v i, (hv i).1⟩ x).mp (hv i).2)
      rcases this; exact h

lemma eval_translationRel_iff {n k} (e : Fin n → ι.Sub M) (r : L'.Rel k) (v : Fin k → Semiterm L' Empty n) :
    Evalbm M (fun i ↦ e i) (ι.translationRel r v) ↔ Structure.rel r fun i ↦ Semiterm.valbm (ι.Sub M) e (v i) := by
  simp [translationRel, Matrix.comp_vecCons', sub_rel_iff, eval_embSubsts, Matrix.constant_eq_singleton]; constructor
  · intro h; exact h (fun i ↦ (Semiterm.valbm (ι.Sub M) e (v i))) (fun i ↦ by simp [eval_varEquals_iff, Matrix.constant_eq_singleton])
  · intro h; intro l H
    have : l = fun i ↦ (Semiterm.valbm (ι.Sub M) e (v i)).val := funext fun i ↦ by
      let z : ι.Sub M := ⟨l i, (H i).1⟩
      have : Evalbm M (z :> fun i ↦ e i) (ι.varEquals (v i)) := (H i).2
      exact congr_arg Subtype.val (eval_varEquals_iff.mp this)
    rcases this
    exact h

lemma eval_translation_iff {p : Semisentence L' n} {e : Fin n → ι.Sub M} :
    Evalbm M (fun i ↦ e i) (ι.translation p) ↔ Evalbm (ι.Sub M) e p := by
  induction p using Semiformula.rec'
    <;> simp [*, Matrix.constant_eq_singleton, eval_substs, eval_translationRel_iff, eval_rel, eval_nrel]
  case hall n p ih =>
    constructor
    · intro h x hx
      exact ih.mp (by simpa [Matrix.comp_vecCons'] using h x hx)
    · intro h x hx
      simpa [Matrix.comp_vecCons'] using ih.mpr (h x hx)
  case hex n p ih =>
    constructor
    · rintro ⟨x, hx, h⟩
      refine ⟨x, hx, ih.mp (by simpa [Matrix.comp_vecCons'] using h)⟩
    · intro ⟨x, hx, h⟩
      refine ⟨x, hx, by simpa [Matrix.comp_vecCons'] using ih.mpr h⟩

lemma models_translation_iff {σ : Sentence L'} :
    M ⊧ₘ (ι.translation σ) ↔ (ι.Sub M) ⊧ₘ σ := by simp [models_iff, ←eval_translation_iff, Matrix.empty_eq]

end semantics

protected def id : Interpretation T L where
  domain := ⊤
  rel (r) := Semiformula.rel r (#·)
  func (f) := “#0 = !!(Semiterm.func f (#·.succ))”
  domain_nonempty := consequence_iff.mpr (by intro M ⟨x⟩ _ _; simp [models_iff]; exact ⟨x, by simp⟩)
  func_defined {k} (f) := consequence_iff_add_eq.mpr fun M _ _ _ _ ↦ by simp [models_iff, Semiterm.val_func]

end Interpretation

class TheoryInterpretation {L L' : Language} [L.Eq] (T : Theory L) (U : Theory L') where
  interpretation : Interpretation T L'
  interpret_theory : ∀ σ ∈ U, T ⊨ interpretation.translation σ

infix:50 " ⊳ " => TheoryInterpretation

namespace TheoryInterpretation

open Interpretation

variable {L L' : Language.{u}} [L.Eq] {T : Theory L} {U : Theory L'} (ι : T ⊳ U)

abbrev translation (p : Semisentence L' n) : Semisentence L n := ι.interpretation.translation p

lemma sub_models_theory {M : Type u} [Nonempty M] [Structure L M] [Structure.Eq L M] (hT : M ⊧ₘ* T) :
    (ι.interpretation.Sub M) ⊧ₘ* U := modelsTheory_iff.mpr fun {σ} hσ ↦ models_translation_iff.mp (ι.interpret_theory σ hσ hT)

lemma theorem_translation {σ : Sentence L'} (h : U ⊨ σ) : T ⊨₌ ι.translation σ :=
  consequence_iff_add_eq.mpr fun M _ _ _ hT ↦
    (@models_translation_iff L L' _ T ι.interpretation M _ _ _ hT σ).mpr <| h <| ι.sub_models_theory hT

open Interpretation

end TheoryInterpretation

end LO.FirstOrder

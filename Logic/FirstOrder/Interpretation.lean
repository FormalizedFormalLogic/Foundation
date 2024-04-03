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
    T + 𝐄𝐪 ⊨ ∃' domain
  func_defined {k} (f : L'.Func k) :
    T + 𝐄𝐪 ⊨ ∀* ((Matrix.conj fun i ↦ domain/[#i]) ⟶ ∃'! (domain/[#0] ⋏ func f))

namespace Interpretation

variable {L L' : Language} [L.Eq] {T : Theory L}

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

protected def id : Interpretation T L where
  domain := ⊤
  rel (r) := Semiformula.rel r (#·)
  func (f) := “#0 = !!(Semiterm.func f (#·.succ))”
  domain_nonempty := consequence_iff.mpr (by intro M ⟨x⟩ _ _; simp [models_iff]; exact ⟨x, by simp⟩)
  func_defined {k} (f) := consequence_iff_add_eq.mpr fun M _ _ _ _ ↦ by simp [models_iff, Semiterm.val_func]

section semantics

open Semiformula

variable {M : Type _} [Nonempty M] [s : Structure L M] [Structure.Eq L M] [M ⊧ₘ* T]

def Dom (x : M) : Prop := PVal! M ![x] ι.domain

variable (M)

lemma dom_iff {x : M} : ι.Dom x ↔ PVal! M ![x] ι.domain := iff_of_eq rfl

abbrev Sub := {x : M // ι.Dom x}

@[simp] lemma pval_sub_domain (x : ι.Sub M) : PVal! M ![x] ι.domain := x.prop

lemma sub_exists : ∃ x : M, ι.Dom x := by
  simpa [Dom, models_iff, eval_substs, Matrix.constant_eq_singleton] using consequence_iff_add_eq.mp ι.domain_nonempty M inferInstance

lemma func_existsUnique_on_dom {k} (f : L'.Func k) : ∀ (v : Fin k → M), (∀ i, ι.Dom (v i)) → ∃! y, ι.Dom y ∧ PVal! M (y :> v) (ι.func f) := by
  simpa [Dom, models_iff, eval_substs, Matrix.constant_eq_singleton] using consequence_iff_add_eq.mp (ι.func_defined f) M inferInstance

lemma func_existsUnique {k} (f : L'.Func k) (v : Fin k → ι.Sub M) : ∃! y : ι.Sub M, PVal! M (y :> fun i ↦ v i) (ι.func f) := by
  have : ∃! y, ι.Dom y ∧ PVal! M (y :> fun i ↦ v i) (ι.func f) := ι.func_existsUnique_on_dom M f (fun i ↦ v i) (fun i ↦ by simp [(v i).prop])
  rcases this.exists with ⟨y, hy, Hy⟩
  exact ExistsUnique.intro ⟨y, hy⟩ (by simpa using Hy) (by simp; intro z hz Hz; exact this.unique ⟨hz, Hz⟩ ⟨hy, Hy⟩)

variable {ι M}

instance : Nonempty (ι.Sub M) := by simpa using ι.sub_exists M

noncomputable instance : Structure L' (ι.Sub M) where
  rel _ r v := Semiformula.PVal! M (fun i ↦ (v i)) (ι.rel r)
  func _ f v := Classical.choose! (ι.func_existsUnique M f v)

lemma sub_rel_iff {k} (r : L'.Rel k) (v : Fin k → ι.Sub M) :
    Structure.rel r v ↔ Semiformula.PVal! M (fun i ↦ (v i)) (ι.rel r) := iff_of_eq rfl

lemma sub_func_iff {k} (f : L'.Func k) (y : ι.Sub M) (v : Fin k → ι.Sub M) :
    y = Structure.func f v ↔ PVal! M (y :> fun i ↦ v i) (ι.func f) := Classical.choose!_eq_iff _

lemma eval_varEquals {t : Semiterm L' Empty n} {y : ι.Sub M} {x : Fin n → ι.Sub M} :
    PVal! M (y :> fun i ↦ x i) (ι.varEquals t) ↔ y = Semiterm.bVal! (ι.Sub M) x t := by
  induction t generalizing x y
  case bvar => simp [varEquals, Subtype.coe_inj]
  case fvar => contradiction
  case func k f w ih =>
    simp [varEquals, eval_embSubsts, Matrix.comp_vecCons', Matrix.constant_eq_singleton, Semiterm.val_func, sub_func_iff]
    constructor
    · intro h; exact h _ (fun i ↦ ⟨ι.pval_sub_domain M _, (@ih i (Semiterm.bVal! (Sub ι M) x (w i)) x).mpr rfl⟩)
    · rintro h v hv
      have : v = fun i ↦ (Semiterm.bVal! (Sub ι M) x (w i)).val :=
        funext fun i ↦ by simpa using congr_arg Subtype.val ((@ih i ⟨v i, (hv i).1⟩ x).mp (hv i).2)
      rcases this; exact h

/-
lemma eval_translationRel {n k} (e : Fin n → ι.Sub M) (r : L'.Rel k) (v : Fin k → Semiterm L' Empty n) :
    PVal! M (fun i ↦ e i) (ι.translationRel r v) ↔ Structure.rel r fun i ↦ Semiterm.bVal! (ι.Sub M) e (v i) := by {
  simp [translationRel, Matrix.comp_vecCons', sub_rel_iff, eval_embSubsts]; constructor
  · intro h; exact h (fun i ↦ (Semiterm.bVal! (ι.Sub M) e (v i))) (fun i ↦ by simp [eval_varEquals, Matrix.constant_eq_singleton])
  · intro h; intro l H
    have : l = fun i ↦ (Semiterm.bVal! (ι.Sub M) e (v i)).val := funext fun i ↦ by {
      have := eval_varEquals.mp (H i)
     }

    }

lemma eval_translation (p : Semisentence L' n) (e : Fin n → ι.Sub M) :
    PVal! M (fun i ↦ e i) (ι.translation p) ↔ PVal! (ι.Sub M) e p := by
  induction p using Semiformula.rec'
    <;> simp [*, Matrix.constant_eq_singleton, eval_substs]
  case hrel r v =>

end semantics

end Interpretation

class Theory.Interpretation {L L' : Language} [L.Eq] (T : Theory L) (U : Theory L') where
  ι : Interpretation T L'
  interpret : ∀ σ ∈ U, T ⊨ ι.translation σ

infix:50 " ⊳ " => Theory.Interpretation

end LO.FirstOrder
-/

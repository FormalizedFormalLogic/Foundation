import Foundation.Propositional.Formula
import Foundation.Logic.Semantics

namespace LO.Propositional

variable {α : Type*}

abbrev ClassicalSemantics.Valuation (α : Type*) := α → Prop

namespace Formula.ClassicalSemantics

open Propositional.ClassicalSemantics (Valuation)

def val (v : Valuation α) : Formula α → Prop
  | atom a  => v a
  | ⊥       => False
  | φ ➝ ψ   => val v φ → val v ψ
  | φ ⋏ ψ   => val v φ ∧ val v ψ
  | φ ⋎ ψ   => val v φ ∨ val v ψ

variable {v : Valuation α} {φ ψ : Formula α}

instance semantics : Semantics (Formula α) (Valuation α) := ⟨fun v ↦ val v⟩

lemma models_iff_val : v ⊧ φ ↔ val v φ := iff_of_eq rfl

instance : Semantics.Tarski (Valuation α) where
  realize_top := by simp [models_iff_val, val]
  realize_bot := by simp [models_iff_val, val]
  realize_and := by simp [models_iff_val, val]
  realize_or  := by simp [models_iff_val, val]
  realize_not := by simp [models_iff_val, val]
  realize_imp := by simp [models_iff_val, val]

@[simp] protected lemma realize_atom : v ⊧ (.atom a) ↔ v a := iff_of_eq rfl

lemma eq_fml_of_eq_atom {v u : Valuation α} (h : ∀ {a : α}, v a ↔ u a) : (∀ {φ : Formula α}, v ⊧ φ ↔ u ⊧ φ) := by
  intro φ;
  induction φ with
  | hatom => apply h;
  | _ => simp [*]

lemma iff_subst_self (s) :
  ((λ a => val v ((.atom a)⟦s⟧)) : Valuation α) ⊧ φ ↔ v ⊧ (φ⟦s⟧) := by
  induction φ with
  | hatom a => simp [val, models_iff_val];
  | hfalsum => simp;
  | himp φ ψ ihφ ihψ =>
    constructor;
    . intro hφψ hφ;
      apply ihψ.mp;
      apply hφψ;
      apply ihφ.mpr;
      exact hφ;
    . intro hφψs hφ;
      apply ihψ.mpr;
      apply hφψs;
      apply ihφ.mp;
      exact hφ;
  | hand φ ψ ihφ ihψ =>
    constructor;
    . rintro ⟨hφ, hψ⟩;
      constructor;
      . apply ihφ.mp hφ;
      . apply ihψ.mp hψ;
    . rintro ⟨hφ, hψ⟩;
      constructor;
      . apply ihφ.mpr hφ;
      . apply ihψ.mpr hψ;
  | hor φ ψ ihφ ihψ =>
    constructor;
    . rintro (hφ | hψ);
      . left; apply ihφ.mp hφ;
      . right; apply ihψ.mp hψ;
    . rintro (hφ | hψ);
      . left; apply ihφ.mpr hφ;
      . right; apply ihψ.mpr hψ;

lemma equiv_of_letterless (hl : φ.letterless) : ∀ v w : Valuation _, v ⊧ φ ↔ w ⊧ φ := by
  intro v w;
  induction φ with
  | hatom a => simp at hl;
  | hfalsum => simp;
  | himp φ ψ ihφ ihψ =>
    simp only [Formula.letterless] at hl;
    replace ihφ := ihφ hl.1;
    replace ihψ := ihψ hl.2;
    simp_all;
  | hand φ ψ ihφ ihψ =>
    simp only [Formula.letterless] at hl;
    replace ihφ := ihφ hl.1;
    replace ihψ := ihψ hl.2;
    simp_all;
  | hor φ ψ ihφ ihψ =>
    simp only [Formula.letterless] at hl;
    replace ihφ := ihφ hl.1;
    replace ihψ := ihψ hl.2;
    simp_all;

end Formula.ClassicalSemantics



section

open Semantics (Valid)
open Formula (atom)
open Formula.ClassicalSemantics
open ClassicalSemantics

variable {v : ClassicalSemantics.Valuation α} {φ ψ : Formula α}

abbrev Formula.isTautology (φ : Formula α) := Valid (ClassicalSemantics.Valuation α) φ

lemma isTautology_subst_of_isTautology (h : φ.isTautology) : ∀ s, (φ⟦s⟧).isTautology := by
  intro s v;
  apply Formula.ClassicalSemantics.iff_subst_self s |>.mp;
  apply h;

lemma iff_isTautology_and : (φ.isTautology) ∧ (ψ.isTautology) ↔ (φ ⋏ ψ).isTautology := by
  constructor;
  . rintro ⟨hφ, hψ⟩ v;
    have := hφ v;
    have := hψ v;
    tauto;
  . intro h;
    constructor;
    . intro v; exact h v |>.1;
    . intro v; exact h v |>.2;

lemma of_isTautology_or : φ.isTautology ∨ ψ.isTautology → (φ ⋎ ψ).isTautology := by
  rintro (hφ | hψ) v;
  . left; exact hφ v;
  . right; exact hψ v;

lemma of_isTautology_imp₂ : (ψ.isTautology) → (φ ➝ ψ).isTautology := by
  intro hψ v h;
  apply hψ;

@[simp]
lemma isTautology_bot : ¬((⊥ : Formula α).isTautology) := by
  intro h;
  have := @h (λ _ => True);
  simp at this;

@[simp]
lemma isTautology_top : (⊤ : Formula α).isTautology := by intro v; simp;

lemma isTautology_of_not_neg_isTautology_of_letterless (hl : φ.letterless) : ¬((∼φ).isTautology) → φ.isTautology := by
  intro h v;
  obtain ⟨w, hw⟩ : ∃ x : Valuation _, x ⊧ φ := by simpa [Formula.isTautology, Valid] using h;
  have H := Formula.ClassicalSemantics.equiv_of_letterless hl;
  apply H w v |>.mp;
  assumption;

lemma neg_isTautology_of_not_isTautology_of_letterless (hl : φ.letterless) : ¬φ.isTautology → (∼φ).isTautology := by
  contrapose!;
  apply isTautology_of_not_neg_isTautology_of_letterless hl;

end


end LO.Propositional

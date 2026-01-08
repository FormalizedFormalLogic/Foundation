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

instance semantics : Semantics (Valuation α) (Formula α) := ⟨fun v ↦ val v⟩

lemma models_iff_val : v ⊧ φ ↔ val v φ := iff_of_eq rfl

instance : Semantics.Tarski (Valuation α) where
  models_verum := by simp [models_iff_val, val]
  models_falsum := by simp [models_iff_val, val]
  models_and := by simp [models_iff_val, val]
  models_or  := by simp [models_iff_val, val]
  models_not := by simp [models_iff_val, val]
  models_imply := by simp [models_iff_val, val]

@[simp] protected lemma models_atom : v ⊧ (.atom a) ↔ v a := iff_of_eq rfl

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

@[grind =>]
lemma equiv_of_letterless (hl : φ.Letterless) : ∀ v w : Valuation _, v ⊧ φ ↔ w ⊧ φ := by
  intro v w;
  induction φ with
  | hatom a => simp at hl;
  | hfalsum => simp;
  | himp φ ψ ihφ ihψ =>
    simp only [Formula.Letterless] at hl;
    replace ihφ := ihφ hl.1;
    replace ihψ := ihψ hl.2;
    simp_all;
  | hand φ ψ ihφ ihψ =>
    simp only [Formula.Letterless] at hl;
    replace ihφ := ihφ hl.1;
    replace ihψ := ihψ hl.2;
    simp_all;
  | hor φ ψ ihφ ihψ =>
    simp only [Formula.Letterless] at hl;
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

abbrev Formula.Tautology (φ : Formula α) := Valid (ClassicalSemantics.Valuation α) φ

@[grind <=]
lemma subst_tautology (h : φ.Tautology) : ∀ s, (φ⟦s⟧).Tautology := by
  intro s v;
  apply Formula.ClassicalSemantics.iff_subst_self s |>.mp;
  apply h;

@[grind =]
lemma iff_and_tautology : (φ ⋏ ψ).Tautology ↔ (φ.Tautology) ∧ (ψ.Tautology) := by
  constructor;
  . intro h;
    constructor;
    . intro v; exact h v |>.1;
    . intro v; exact h v |>.2;
  . rintro ⟨hφ, hψ⟩ v;
    have := hφ v;
    have := hψ v;
    tauto;

@[grind <=]
lemma or_tautology_of : φ.Tautology ∨ ψ.Tautology → (φ ⋎ ψ).Tautology := by
  rintro (hφ | hψ) v;
  . left; exact hφ v;
  . right; exact hψ v;

@[grind <=]
lemma imp_tautology_of : (ψ.Tautology) → (φ ➝ ψ).Tautology := by
  intro hψ v h;
  apply hψ;
alias tautology_afortiori := imp_tautology_of

@[simp, grind .]
lemma not_bot_tautology : ¬((⊥ : Formula α).Tautology) := by
  intro h;
  have := @h (λ _ => True);
  simp at this;

@[simp, grind .]
lemma top_tautology : (⊤ : Formula α).Tautology := by intro v; simp;

@[grind =>]
lemma tautology_of_letterless_of_not_neg_tautology (hl : φ.Letterless) : ¬((∼φ).Tautology) → φ.Tautology := by
  intro h v;
  obtain ⟨w, hw⟩ : ∃ x : Valuation _, x ⊧ φ := by simpa [Formula.Tautology, Valid] using h;
  have H := Formula.ClassicalSemantics.equiv_of_letterless hl;
  apply H w v |>.mp;
  assumption;

@[grind =>]
lemma neg_tautology_of_letterless_of_tautology (hl : φ.Letterless) : ¬φ.Tautology → (∼φ).Tautology := by
  contrapose!;
  apply tautology_of_letterless_of_not_neg_tautology hl;

end


end LO.Propositional

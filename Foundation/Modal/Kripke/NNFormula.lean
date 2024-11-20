import Foundation.Modal.NNFormula
import Foundation.Modal.Kripke.Semantics

namespace LO.Modal

open System

variable {φ ψ : NNFormula ℕ}

namespace NNFormula.Kripke

def Satisfies (M : Kripke.Model) (x : M.World) : NNFormula ℕ → Prop
  | atom a  =>  M x a
  | natom a => ¬M x a
  | ⊤       => True
  | ⊥       => False
  | φ ⋎ ψ   => Satisfies M x φ ∨ Satisfies M x ψ
  | φ ⋏ ψ   => Satisfies M x φ ∧ Satisfies M x ψ
  | □φ      => ∀ y, x ≺ y → Satisfies M y φ
  | ◇φ      => ∃ y, x ≺ y ∧ (Satisfies M y φ)

namespace Satisfies

variable {M : Kripke.Model} {x : M.World}

protected instance semantics : Semantics (NNFormula ℕ) (M.World) := ⟨λ x ↦ Satisfies M x⟩

protected lemma iff_models : x ⊧ φ ↔ Satisfies M x φ := iff_of_eq rfl

protected lemma top_def : x ⊧ ⊤ := by simp [Satisfies.iff_models, Satisfies];

protected lemma bot_def : ¬x ⊧ ⊥ := by simp [Satisfies.iff_models, Satisfies];

protected lemma or_def : x ⊧ φ ⋎ ψ ↔ x ⊧ φ ∨ x ⊧ ψ := by simp [Satisfies.iff_models, Satisfies];

protected lemma and_def : x ⊧ φ ⋏ ψ ↔ x ⊧ φ ∧ x ⊧ ψ := by simp [Satisfies.iff_models, Satisfies];

protected lemma box_def : x ⊧ □φ ↔ ∀ y, x ≺ y → y ⊧ φ := by simp [Satisfies.iff_models, Satisfies];

protected lemma dia_def : x ⊧ ◇φ ↔ ∃ y, x ≺ y ∧ y ⊧ φ := by simp [Satisfies.iff_models, Satisfies];

protected lemma neg_def : x ⊧ ∼φ ↔ ¬x ⊧ φ := by
  induction φ using NNFormula.rec' generalizing x with
  | hOr φ ψ ihφ ihψ =>
    simp only [DeMorgan.or, Satisfies.or_def, not_or];
    constructor;
    . rintro ⟨h₁, h₂⟩;
      exact ⟨ihφ.mp h₁, ihψ.mp h₂⟩;
    . rintro ⟨h₁, h₂⟩;
      exact ⟨ihφ.mpr h₁, ihψ.mpr h₂⟩;
  | hAnd φ ψ ihφ ihψ =>
    simp only [DeMorgan.and, Satisfies.and_def, not_and_or];
    constructor;
    . rintro (h₁ | h₂);
      . left; exact ihφ.mp h₁;
      . right; exact ihψ.mp h₂;
    . rintro (h₁ | h₂);
      . left; exact ihφ.mpr h₁;
      . right; exact ihψ.mpr h₂;
  | hBox φ ihφ =>
    simp only [ModalDeMorgan.box, Satisfies.box_def];
    push_neg;
    constructor;
    . intro h;
      obtain ⟨y, Rxy, hy⟩ := h;
      use y;
      constructor;
      . exact Rxy;
      . apply ihφ.mp;
        exact hy;
    . rintro ⟨y, Rxy, h⟩;
      use y;
      constructor;
      . exact Rxy;
      . apply ihφ.mpr;
        exact h;
  | hDia φ ihφ =>
    simp only [ModalDeMorgan.dia, Satisfies.dia_def, not_exists, not_and];
    constructor;
    . intro h y Rxy;
      apply ihφ.mp;
      exact h y Rxy;
    . intro h y Rxy;
      apply ihφ.mpr;
      exact h y Rxy;
  | _ => simp [Satisfies.iff_models, Satisfies];

protected lemma imp_def : x ⊧ φ ➝ ψ ↔ x ⊧ φ → x ⊧ ψ := by
  simp [←NNFormula.imp_eq, NNFormula.imp, Satisfies.or_def, Satisfies.neg_def];
  tauto;

protected instance : Semantics.Tarski (M.World) where
  realize_top := λ _ => Satisfies.top_def
  realize_bot := λ _ => Satisfies.bot_def
  realize_or  := Satisfies.or_def
  realize_and := Satisfies.and_def
  realize_imp := Satisfies.imp_def
  realize_not := Satisfies.neg_def

end Satisfies



end NNFormula.Kripke

end LO.Modal

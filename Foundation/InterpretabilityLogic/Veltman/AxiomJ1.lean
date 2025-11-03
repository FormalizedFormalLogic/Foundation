import Foundation.InterpretabilityLogic.Veltman.Basic

namespace LO.InterpretabilityLogic.Veltman

open Veltman Formula.Veltman

variable {F : Veltman.Frame} {φ ψ χ : Formula ℕ}

namespace Frame

class HasAxiomJ1 (F : Frame) : Prop where
  S_refl : ∀ x, IsRefl _ (F.S x)
export HasAxiomJ1 (S_refl)

end Frame

@[simp high, grind]
lemma validate_axiomJ1_of_J1 [F.HasAxiomJ1] : F ⊧ Axioms.J1 φ ψ := by
  intro V x h y hy;
  use y;
  constructor;
  . apply F.S_refl x |>.refl;
  . apply h;
    . exact y.2;
    . exact hy;

lemma Frame.HasAxiomJ1.of_validate_axiomJ1 (h : F ⊧ Axioms.J1 (.atom 0) (.atom 1)) : F.HasAxiomJ1 := by
  constructor;
  intro x;
  constructor;
  intro y;
  obtain ⟨z, Sxyz, hz⟩ := @h (λ u _ => u = y) x (by tauto) y (by tauto);
  replace hz : z = y := by
    simp only [Satisfies] at hz;
    grind;
  apply hz ▸ Sxyz;

end LO.InterpretabilityLogic.Veltman

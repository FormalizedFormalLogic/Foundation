module

public import Foundation.InterpretabilityLogic.Veltman.Basic

@[expose] public section

namespace LO.InterpretabilityLogic.Veltman

open Veltman Formula.Veltman

variable {F : Veltman.Frame} {φ ψ χ : Formula ℕ}

namespace Frame

class HasAxiomJ1 (F : Frame) : Prop where
  S_J1 : ∀ {w x : F.World}, w ≺ x → x ≺[w] x
export HasAxiomJ1 (S_J1)

end Frame

@[simp high, grind .]
lemma validate_axiomJ1_of_J1 [F.HasAxiomJ1] : F ⊧ Axioms.J1 φ ψ := by
  intro V x h₁ y Rxy h₂;
  use y;
  constructor;
  . apply F.S_J1; assumption;
  . apply h₁ <;> simpa;

lemma Frame.HasAxiomJ1.of_validate_axiomJ1 (h : F ⊧ Axioms.J1 (.atom 0) (.atom 1)) : F.HasAxiomJ1 := by
  constructor;
  intro x y Rxy;
  obtain ⟨z, Sxyz, hz⟩ := @h (λ u _ => u = y) x (by tauto) y Rxy (by tauto);
  replace hz : z = y := by
    simp only [Satisfies] at hz;
    grind;
  apply hz ▸ Sxyz;

end LO.InterpretabilityLogic.Veltman
end

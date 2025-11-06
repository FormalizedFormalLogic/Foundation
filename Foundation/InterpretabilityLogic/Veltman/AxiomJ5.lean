import Foundation.InterpretabilityLogic.Veltman.Basic

namespace LO.InterpretabilityLogic.Veltman

open Veltman Formula.Veltman

variable {F : Veltman.Frame} {φ ψ χ : Formula ℕ}

namespace Frame

class HasAxiomJ5 (F : Frame) : Prop where
  S_J5 : ∀ {w x y : F.World}, w ≺ x → x ≺ y → x ≺[w] y
export HasAxiomJ5 (S_J5)

end Frame

@[simp high, grind .]
lemma validate_axiomJ5_of_J5 [F.HasAxiomJ5] : F ⊧ Axioms.J5 φ := by
  rintro V x y Rxy h;
  obtain ⟨z, Ryz, hz⟩ := Satisfies.dia_def.mp h;
  use z;
  constructor
  . apply Veltman.Frame.S_J5 <;> simpa;
  . assumption;

lemma Frame.HasAxiomJ5.of_validate_axiomJ5 (h : F ⊧ Axioms.J5 (.atom 0)) : F.HasAxiomJ5 := by
  constructor;
  intro w x y Rwx Rwy;
  obtain ⟨z, Swxz, hz⟩ := @h (λ u _ => u = y) w x (by tauto) (by tauto);
  replace hz : z = y := by
    simp only [Satisfies] at hz;
    grind;
  apply hz ▸ Swxz;

end LO.InterpretabilityLogic.Veltman

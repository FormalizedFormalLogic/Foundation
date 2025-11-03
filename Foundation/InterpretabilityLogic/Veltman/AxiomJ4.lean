import Foundation.InterpretabilityLogic.Veltman.Basic

namespace LO.InterpretabilityLogic.Veltman

open Veltman Formula.Veltman

variable {F : Veltman.Frame} {φ ψ χ : Formula ℕ}

namespace Frame

class HasAxiomJ4 (F : Frame) : Prop where
  S_J4 : ∀ {w x y}, (F.S w x y) → (w ≺ y)
export HasAxiomJ4 (S_J4)

end Frame

@[simp high, grind]
lemma validate_axiomJ4_of_HasAxiomJ4 [F.HasAxiomJ4] : F ⊧ Axioms.J4 φ ψ := by
  intro V x h₁ h₂;
  replace ⟨z, Rxz, h₂⟩ := Satisfies.dia_def.mp h₂;
  obtain ⟨w, Sxzw, hw⟩ := h₁ z Rxz h₂;
  apply Satisfies.dia_def.mpr;
  use w;
  constructor;
  . apply F.S_J4 Sxzw;
  . assumption;

@[simp high, grind]
lemma validate_axiomJ4Plus_of_HasAxiomJ4 [F.HasAxiomJ4] : F ⊧ Axioms.J4Plus φ ψ χ := by
  intro V x h₁ h₂ y Rxy h₃;
  obtain ⟨z, Sxyz, hz⟩ := h₂ y Rxy h₃;
  use z;
  constructor;
  . assumption;
  . apply h₁ z (F.S_J4 Sxyz) hz;

@[simp high, grind]
lemma Frame.HasAxiomJ4.of_validate_axiomJ4 (h : F ⊧ Axioms.J4 (.atom 0) (.atom 1)) : F.HasAxiomJ4 := by
  constructor;
  intro w x y Swxy;
  have := @h (λ u a => match a with | 0 => u = x | 1 => u = y | _ => False) w ?_ ?_;
  . obtain ⟨z, Rwz, hz⟩ := Satisfies.dia_def.mp this;
    replace hz : z = y := by
      simp [Semantics.Models, Satisfies] at hz;
      grind;
    apply hz ▸ Rwz;
  . suffices ∀ (y_1 : F.World), w ≺ y_1 → y_1 = x → F.S w y_1 y by simpa [Satisfies];
    rintro z Rwz rfl;
    assumption;
  . apply Satisfies.dia_def.mpr;
    use x;
    constructor;
    . apply F.S_cond Swxy;
    . tauto;

open Formula (atom)
lemma validate_axiomJ4_of_validate_axiomJ4Plus {F : Veltman.Frame} (h : F ⊧ Axioms.J4Plus (.atom 1) (.atom 2) (.atom 0)) : F ⊧ Axioms.J4 (.atom 0) (.atom 1) := by

  intro V x h₁ h₂;
  dsimp [Axioms.J4Plus] at h;

  have := h V x (by sorry);
  replace ⟨z, Rxz, h₂⟩ := Satisfies.dia_def.mp h₂;
  obtain ⟨w, Sxzw, hw⟩ := h₁ z Rxz h₂;
  apply Satisfies.dia_def.mpr;
  use w;
  constructor;
  . apply F.trans Rxz;
    sorry;
  . assumption;

end LO.InterpretabilityLogic.Veltman

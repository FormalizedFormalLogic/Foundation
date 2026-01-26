module

public import Foundation.InterpretabilityLogic.Veltman.Basic
public import Foundation.InterpretabilityLogic.Veltman.Logic.ILMinus


@[expose] public section

namespace LO.InterpretabilityLogic.Veltman

open Veltman Formula.Veltman

variable {F : Veltman.Frame} {φ ψ χ : Formula ℕ}

namespace Frame

class HasAxiomJ4 (F : Frame) : Prop where
  S_J4 : ∀ {w x y : F.World}, x ≺[w] y → w ≺ y
export HasAxiomJ4 (S_J4)

end Frame

@[simp high, grind .]
lemma validate_axiomJ4Plus_of_HasAxiomJ4 [F.HasAxiomJ4] : F ⊧ Axioms.J4Plus φ ψ χ := by
  intro V x h₁ h₂ y Rxy h₃;
  obtain ⟨z, Sxyz, hz⟩ := h₂ y Rxy h₃;
  use z;
  constructor;
  . assumption;
  . apply h₁ z (F.S_J4 Sxyz) hz;

open Hilbert.Minimal in
lemma validate_axiomJ4_of_validate_axiomJ4Plus (h : F ⊧ Axioms.J4Plus (.atom 0) (.atom 1) (.atom 2)) : F ⊧ Axioms.J4 φ ψ := by
  apply Hilbert.Minimal.Veltman.soundness_frame (Ax := ILMinus_J4Plus.axioms);
  . constructor;
    intro φ hφ;
    rcases (by simpa [buildAxioms] using hφ) with (rfl | rfl | rfl | rfl) <;> grind;
  . simp;

@[simp high, grind .]
lemma validate_axiomJ4_of_HasAxiomJ4 [F.HasAxiomJ4] : F ⊧ Axioms.J4 φ ψ := by
  apply validate_axiomJ4_of_validate_axiomJ4Plus;
  apply validate_axiomJ4Plus_of_HasAxiomJ4;

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

lemma Frame.HasAxiomJ4.of_validate_axiomJ4Plus (h : F ⊧ Axioms.J4Plus (.atom 0) (.atom 1) (.atom 2)) : F.HasAxiomJ4 := by
  apply Frame.HasAxiomJ4.of_validate_axiomJ4;
  apply validate_axiomJ4_of_validate_axiomJ4Plus h;

lemma validate_axiomJ4Plus_of_validate_axiomJ4 (h : F ⊧ Axioms.J4 (.atom 0) (.atom 1)) : F ⊧ Axioms.J4Plus φ ψ χ := by
  apply @validate_axiomJ4Plus_of_HasAxiomJ4 F _ _ _ $ Frame.HasAxiomJ4.of_validate_axiomJ4 h;

lemma validate_axiomJ4_iff_validate_axiomJ4Plus : (F ⊧ Axioms.J4 (.atom 0) (.atom 1)) ↔ (F ⊧ Axioms.J4Plus (.atom 0) (.atom 1) (.atom 2)) := ⟨
  fun h ↦ validate_axiomJ4Plus_of_validate_axiomJ4 h,
  fun h ↦ validate_axiomJ4_of_validate_axiomJ4Plus h
⟩

end LO.InterpretabilityLogic.Veltman
end

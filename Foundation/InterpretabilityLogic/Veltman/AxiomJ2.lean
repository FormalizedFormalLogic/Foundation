module
import Foundation.InterpretabilityLogic.Veltman.AxiomJ4

namespace LO.InterpretabilityLogic.Veltman

open Veltman Formula.Veltman

variable {F : Veltman.Frame} {φ ψ χ : Formula ℕ}

namespace Frame

class HasAxiomJ2 (F : Frame) extends F.HasAxiomJ4 where
  S_J2 : ∀ {w x y z : F.World}, x ≺[w] y → y ≺[w] z → x ≺[w] z
export HasAxiomJ2 (S_J2)

end Frame

@[simp high, grind .]
lemma validate_axiomJ2Plus_of_HasAxiomJ2 [F.HasAxiomJ2] : F ⊧ Axioms.J2Plus φ ψ χ := by
  intro V x h₁ h₂ y Rxy h₃;
  replace ⟨z, Sxyz, h₃⟩ := h₁ y Rxy h₃;
  rcases Satisfies.or_def.mp h₃ with (h₃ | h₃);
  . obtain ⟨u, Sxzu, _⟩ := h₂ z (F.S_J4 Sxyz) h₃;
    use u;
    constructor;
    . apply F.S_J2 Sxyz Sxzu;
    . tauto;
  . use z;
    tauto;

open Hilbert.Minimal in
lemma validate_axiomJ2_of_validate_axiomJ2Plus (h : F ⊧ Axioms.J2Plus (.atom 0) (.atom 1) (.atom 2)) : F ⊧ Axioms.J2 φ ψ χ := by
  apply Hilbert.Minimal.Veltman.soundness_frame (Ax := ILMinus_J2Plus.axioms);
  . constructor;
    intro φ hφ;
    rcases (by simpa [buildAxioms] using hφ) with (rfl | rfl | rfl | rfl) <;> grind;
  . simp;

@[simp high]
lemma validate_axiomJ2_of_HasAxiomJ2 [F.HasAxiomJ2] : F ⊧ Axioms.J2 φ ψ χ := by
  apply @validate_axiomJ2_of_validate_axiomJ2Plus F _ _ _ $ validate_axiomJ2Plus_of_HasAxiomJ2;

open Hilbert.Minimal in
lemma validate_axiomJ4_of_validate_axiomJ2 (h : F ⊧ Axioms.J2 (.atom 0) (.atom 1) (.atom 2)) : F ⊧ Axioms.J4 φ ψ := by
  apply Hilbert.Minimal.Veltman.soundness_frame (Ax := ILMinus_J2.axioms);
  . constructor;
    intro φ hφ;
    rcases (by simpa [buildAxioms] using hφ) with (rfl | rfl | rfl | rfl) <;> grind;
  . simp;

open Formula (atom) in
lemma Frame.HasAxiomJ2.of_validate_axiomJ2 (h : F ⊧ Axioms.J2 (.atom 0) (.atom 1) (.atom 2)) : F.HasAxiomJ2 := by
  exact {
    S_J4 := Frame.HasAxiomJ4.of_validate_axiomJ4 (validate_axiomJ4_of_validate_axiomJ2 h) |>.S_J4
    S_J2 := by
      intro w x y z Swxy Swyz;
      have := @h (λ u a => match a with | 0 => u = x | 1 => u = y | 2 => u = z | _ => False) w;
      have := @this ?_ ?_ x ?_ $ by tauto;
      . obtain ⟨u, Swxu, hu⟩ := this;
        have : u = z := by simpa [Semantics.Models, Satisfies] using hu;
        apply this ▸ Swxu;
      . intro v Rwv hv;
        have : v = x := by simpa [Semantics.Models, Satisfies] using hv;
        use y;
        constructor;
        . apply this ▸ Swxy;
        . tauto;
      . intro v Rwv hv;
        have : v = y := by simpa [Semantics.Models, Satisfies] using hv;
        use z;
        constructor;
        . apply this ▸ Swyz;
        . tauto;
      . apply F.S_cond Swxy;
  }

lemma Frame.HasAxiomJ2.of_validate_axiomJ2Plus (h : F ⊧ Axioms.J2Plus (.atom 0) (.atom 1) (.atom 2)) : F.HasAxiomJ2 := by
  apply Frame.HasAxiomJ2.of_validate_axiomJ2;
  apply validate_axiomJ2_of_validate_axiomJ2Plus h;

lemma validate_axiomJ2Plus_of_validate_axiomJ2 (h : F ⊧ Axioms.J2 (.atom 0) (.atom 1) (.atom 2)) : F ⊧ Axioms.J2Plus φ ψ χ := by
  apply @validate_axiomJ2Plus_of_HasAxiomJ2 F _ _ _ $ Frame.HasAxiomJ2.of_validate_axiomJ2 h;

lemma validate_axiomJ2_iff_validate_axiomJ2Plus : (F ⊧ Axioms.J2 (.atom 0) (.atom 1) (.atom 2)) ↔ (F ⊧ Axioms.J2Plus (.atom 0) (.atom 1) (.atom 2)) := ⟨
  fun h ↦ validate_axiomJ2Plus_of_validate_axiomJ2 h,
  fun h ↦ validate_axiomJ2_of_validate_axiomJ2Plus h
⟩

end LO.InterpretabilityLogic.Veltman

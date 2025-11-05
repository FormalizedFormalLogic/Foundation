import Foundation.InterpretabilityLogic.Veltman.Basic
import Foundation.InterpretabilityLogic.Veltman.Logic.IL

namespace LO.InterpretabilityLogic.Veltman

open Veltman Formula.Veltman

variable {F : Veltman.Frame} {φ ψ χ : Formula ℕ}

namespace Frame

class HasAxiomM (F : Frame) : Prop where
  S_M : ∀ {w x y z: F.World}, x ≺[w] y → y ≺ z → x ≺ z
export HasAxiomM (S_M)

end Frame

@[simp high, grind]
lemma validate_axiomM_of_HasAxiomM [F.HasAxiomM] : F ⊧ Axioms.M φ ψ χ := by
  intro V x h₁ y Rxy h₂;
  replace ⟨h₂₁, h₂₂⟩ := Satisfies.and_def.mp h₂;
  obtain ⟨z, Sxyz, hz⟩ := h₁ y Rxy h₂₁;
  use z;
  constructor;
  . assumption;
  . apply Satisfies.and_def.mpr;
    constructor;
    . assumption;
    . intro w Rzw;
      apply h₂₂;
      apply F.S_M Sxyz Rzw;

open Hilbert.Minimal in
lemma validate_axiomKM1_of_validate_axiomM (h : F ⊧ Axioms.M (.atom 0) (.atom 1) (.atom 2)) : F ⊧ Axioms.KM1 φ ψ := by
  apply Hilbert.Minimal.Veltman.soundness_frame (Ax := ILMinus_M.axioms);
  . constructor;
    intro φ hφ;
    rcases (by simpa [buildAxioms] using hφ) with (rfl | rfl | rfl) <;> grind;
  . simp;

@[simp high, grind]
lemma validate_axiomKM1_of_HasAxiomM [F.HasAxiomM] : F ⊧ Axioms.KM1 φ ψ := by
  apply validate_axiomKM1_of_validate_axiomM;
  apply validate_axiomM_of_HasAxiomM;

open Formula (atom) in
lemma Frame.HasAxiomM.of_validate_axiomKM1 (h : F ⊧ Axioms.KM1 (.atom 0) (.atom 1)) : F.HasAxiomM := by
  constructor;
  dsimp [Axioms.KM1] at h;
  intro w x y z Swxy Ryz;
  have := @h (λ u a => match a with | 0 => u = x | 1 => u = y ∨ u = z | _ => False) w ?_ x ?_;
  . obtain ⟨v, Rwv, hv⟩ := Satisfies.dia_def.mp $ this (by tauto)
    rcases hv with (hv | hv);
    . apply F.trans Rwv;
      grind;
    . grind;
  . intro v Rwv hv;
    use y;
    constructor;
    . replace hv : v = x := by simpa [Semantics.Models, Satisfies] using hv;
      exact hv ▸ Swxy;
    . apply Satisfies.dia_def.mpr;
      use z;
      constructor;
      . assumption;
      . tauto;
  . apply F.S_cond Swxy;

lemma Frame.HasAxiomM.of_validate_axiomM (h : F ⊧ Axioms.M (.atom 0) (.atom 1) (.atom 2)) : F.HasAxiomM := by
  apply Frame.HasAxiomM.of_validate_axiomKM1;
  apply validate_axiomKM1_of_validate_axiomM h;

end LO.InterpretabilityLogic.Veltman

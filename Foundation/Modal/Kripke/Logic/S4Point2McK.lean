import Foundation.Modal.Kripke.Logic.S4McK
import Foundation.Modal.Kripke.Logic.S4Point2

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

variable {F : Kripke.Frame}

protected class Frame.IsS4Point2McK (F : Kripke.Frame) extends F.IsReflexive, F.IsTransitive, F.SatisfiesMcKinseyCondition, F.IsPiecewiseStronglyConvergent where

protected abbrev FrameClass.S4Point2McK : FrameClass := { F | F.IsS4Point2McK }

end Kripke


namespace Hilbert.S4Point2McK.Kripke

instance : Sound (Hilbert.S4Point2McK) FrameClass.S4Point2McK := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_⟩ _ (rfl | rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomMcK_of_satisfiesMcKinseyCondition;
  . exact validate_AxiomPoint2_of_confluent;

instance : Entailment.Consistent Hilbert.S4Point2McK :=
  consistent_of_sound_frameclass FrameClass.S4Point2McK $ by
    use whitepoint;
    constructor;

instance : Canonical (Hilbert.S4Point2McK) FrameClass.S4Point2McK := ⟨by constructor⟩

instance : Complete (Hilbert.S4Point2McK) FrameClass.S4Point2McK := inferInstance


instance : Hilbert.S4McK ⪱ Hilbert.S4Point2McK := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_subset_axioms; intro φ; aesop;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Point2 (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.S4McK);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => x = 0 ∨ x = y⟩, λ w a => w = 1⟩;
      use M, 0;
      constructor
      . exact {
          refl := by omega;
          trans := by omega;
          mckinsey := by
            intro x;
            simp only [M];
            match x with
            | 0 => use 1; tauto;
            | 1 => use 1; tauto;
            | 2 => use 2; tauto;
        }
      . suffices ∃ x, (0 : M.World) ≺ x ∧ (∀ y, x ≺ y → y = 1) ∧ ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 1 by
          simpa [M, Semantics.Realize, Satisfies];
        use 1;
        refine ⟨?_, ?_, ?_⟩;
        . omega;
        . simp [M];
          omega;
        . use 2;
          omega;

instance : Hilbert.S4Point2 ⪱ Hilbert.S4Point2McK := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_subset_axioms; intro φ; aesop;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.McK (.atom 0))
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.S4Point2);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . refine {
          refl := by tauto;
          trans := by tauto;
          ps_convergent := by tauto;
        }
      . suffices ∃ x : M, x ≠ 0 by simpa [M, Semantics.Realize, Satisfies];
        use 1;
        trivial;

end Hilbert.S4Point2McK.Kripke

end LO.Modal

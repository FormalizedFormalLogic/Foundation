import Foundation.Modal.Kripke.Logic.S4McK
import Foundation.Modal.Kripke.Logic.S4Point2

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

variable {F : Kripke.Frame}

class Frame.IsS4Point2McK (F : Kripke.Frame) extends F.IsReflexive, F.IsTransitive, F.SatisfiesMcKinseyCondition, F.IsPiecewiseStronglyConvergent where

abbrev FrameClass.preorder_confluent_mckinsey : FrameClass := { F | F.IsS4Point2McK }

end Kripke


namespace Logic.S4Point2McK.Kripke

instance sound : Sound (Logic.S4Point2McK) Kripke.FrameClass.preorder_confluent_mckinsey := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_⟩ _ (rfl | rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomMcK_of_satisfiesMcKinseyCondition;
  . exact validate_AxiomPoint2_of_confluent;

instance consistent : Entailment.Consistent Logic.S4Point2McK :=
  consistent_of_sound_frameclass FrameClass.preorder_confluent_mckinsey $ by
    use whitepoint;
    constructor;

instance canonical : Canonical (Logic.S4Point2McK) Kripke.FrameClass.preorder_confluent_mckinsey := ⟨by constructor⟩

instance complete : Complete (Logic.S4Point2McK) Kripke.FrameClass.preorder_confluent_mckinsey := inferInstance

lemma preorder_confluent_mckinsey : Logic.S4Point2McK = FrameClass.preorder_confluent_mckinsey.logic := eq_hilbert_logic_frameClass_logic

instance : Logic.S4McK ⪱ Logic.S4Point2McK := by
  constructor;
  . apply Hilbert.weakerThan_of_subset_axioms; intro φ; aesop;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.S4Point2McK ⊢! φ ∧ ¬Kripke.FrameClass.S4McK ⊧ φ by simpa [S4McK.Kripke.preorder_mckinsey];
    use (Axioms.Point2 (.atom 0));
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
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

instance : Logic.S4Point2 ⪱ Logic.S4Point2McK := by
  constructor;
  . apply Hilbert.weakerThan_of_subset_axioms; intro φ; aesop;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.S4Point2McK ⊢! φ ∧ ¬FrameClass.S4Point2 ⊧ φ by simpa [S4Point2.Kripke.confluent_preorder];
    use (Axioms.McK (.atom 0))
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
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

end Logic.S4Point2McK.Kripke

end LO.Modal

import Foundation.Modal.Kripke.Logic.S4M
import Foundation.Modal.Kripke.Logic.S4Point2

namespace LO.Modal

open Kripke
open Hilbert.Kripke


namespace Kripke

variable {F : Kripke.Frame}

class Frame.IsS4Point2M (F : Kripke.Frame) extends F.IsReflexive, F.IsTransitive, F.SatisfiesMcKinseyCondition, F.IsPiecewiseStronglyConvergent where

abbrev FrameClass.preorder_confluent_mckinsey : FrameClass := { F | F.IsS4Point2M }

end Kripke


namespace Hilbert.S4Point2M.Kripke

instance sound : Sound (Hilbert.S4Point2M) Kripke.FrameClass.preorder_confluent_mckinsey := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_⟩ _ (rfl | rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomM_of_satisfiesMcKinseyCondition;
  . exact validate_AxiomPoint2_of_confluent;

instance consistent : Entailment.Consistent (Hilbert.S4Point2M) :=
  consistent_of_sound_frameclass FrameClass.preorder_confluent_mckinsey $ by
    use whitepoint;
    constructor;

instance canonical : Canonical (Hilbert.S4Point2M) Kripke.FrameClass.preorder_confluent_mckinsey := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor;
⟩

instance complete : Complete (Hilbert.S4Point2M) Kripke.FrameClass.preorder_confluent_mckinsey := inferInstance

end Hilbert.S4Point2M.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma S4Point2M.Kripke.preorder_confluent_mckinsey : Logic.S4Point2M = FrameClass.preorder_confluent_mckinsey.logic := eq_hilbert_logic_frameClass_logic

@[simp]
theorem S4Point2M.proper_extension_of_S4M : Logic.S4M ⊂ Logic.S4Point2M := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.S4Point2M ⊢! φ ∧ ¬Kripke.FrameClass.S4M ⊧ φ by
      rw [S4M.Kripke.preorder_mckinsey];
      tauto;
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

@[simp]
theorem S4Point2M.proper_extension_of_S4Point2 : Logic.S4Point2 ⊂ Logic.S4Point2M := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.S4Point2M ⊢! φ ∧ ¬FrameClass.S4Point2 ⊧ φ by
      rw [S4Point2.Kripke.confluent_preorder];
      tauto;
    use (Axioms.M (.atom 0))
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

end Logic

end LO.Modal

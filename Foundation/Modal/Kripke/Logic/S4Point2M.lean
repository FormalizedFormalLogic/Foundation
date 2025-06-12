import Foundation.Modal.Kripke.Logic.S4M
import Foundation.Modal.Kripke.Logic.S4Point2

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open GeachConfluent

abbrev Kripke.FrameClass.preorder_confluent_mckinsey : FrameClass := { F | IsPreorder _ F ∧ IsConfluent _ F ∧ SatisfiesMcKinseyCondition _ F }

namespace Hilbert.S4Point2M.Kripke

instance sound : Sound (Hilbert.S4Point2M) Kripke.FrameClass.preorder_confluent_mckinsey := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _⟩ _ (rfl | rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomM_of_satisfiesMcKinseyCondition;
  . exact validate_AxiomPoint2_of_confluent;

instance consistent : Entailment.Consistent (Hilbert.S4Point2M) :=
  consistent_of_sound_frameclass FrameClass.preorder_confluent_mckinsey $ by
    use whitepoint;
    refine ⟨inferInstance, inferInstance, inferInstance⟩;

instance canonical : Canonical (Hilbert.S4Point2M) Kripke.FrameClass.preorder_confluent_mckinsey := ⟨by
  apply Set.mem_setOf_eq.mpr;
  refine ⟨?_, ?_, ?_⟩;
  . constructor;
  . infer_instance;
  . infer_instance;
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
  . suffices ∃ φ, Hilbert.S4Point2M ⊢! φ ∧ ¬Kripke.FrameClass.preorder_mckinsey ⊧ φ by
      rw [S4M.Kripke.preorder_mckinsey];
      tauto;
    use (Axioms.Point2 (.atom 0));
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => x = 0 ∨ x = y⟩, λ w a => w = 1⟩;
      use M, 0;
      constructor
      . refine ⟨?_, ⟨?_⟩⟩;
        . apply isPreorder_iff _ _ |>.mpr;
          refine ⟨⟨?_⟩, ⟨?_⟩⟩ <;> omega;
        . intro x;
          match x with
          | 0 => use 1; simp_all [M];
          | 1 => use 1; simp_all [M];
          | 2 => use 2; simp_all [M];
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
  . suffices ∃ φ, Hilbert.S4Point2M ⊢! φ ∧ ¬FrameClass.confluent_preorder ⊧ φ by
      rw [S4Point2.Kripke.confluent_preorder];
      tauto;
    use (Axioms.M (.atom 0))
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . refine ⟨?_, ⟨?_⟩⟩;
        . apply isPreorder_iff _ _ |>.mpr;
          refine ⟨⟨?_⟩, ⟨?_⟩⟩ <;> tauto;
        . tauto;
      . suffices ∃ x : M, x ≠ 0 by simpa [M, Semantics.Realize, Satisfies];
        use 1;
        trivial;

end Logic

end LO.Modal

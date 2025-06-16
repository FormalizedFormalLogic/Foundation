import Foundation.Modal.Kripke.Logic.S4Point3M
import Foundation.Modal.Kripke.Logic.S4Point4

namespace LO.Modal

open Kripke
open Hilbert.Kripke


abbrev Kripke.FrameClass.preorder_sobocinski_mckinsey : FrameClass := { F | F.IsPreorder ∧ SatisfiesSobocinskiCondition _ F ∧ SatisfiesMcKinseyCondition _ F }

namespace Hilbert.S4Point4M.Kripke

instance sound : Sound (Hilbert.S4Point4M) Kripke.FrameClass.preorder_sobocinski_mckinsey := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _⟩ _ (rfl | rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomM_of_satisfiesMcKinseyCondition;
  . exact validate_axiomPoint4_of_satisfiesSobocinskiCondition;

instance consistent : Entailment.Consistent (Hilbert.S4Point4M) :=
  consistent_of_sound_frameclass FrameClass.preorder_sobocinski_mckinsey $ by
    use whitepoint;
    refine ⟨inferInstance, inferInstance, inferInstance⟩;

instance canonical : Canonical (Hilbert.S4Point4M) Kripke.FrameClass.preorder_sobocinski_mckinsey := ⟨by
  apply Set.mem_setOf_eq.mpr;
  refine ⟨?_, ?_, ?_⟩;
  . constructor;
  . infer_instance;
  . infer_instance;
⟩

instance complete : Complete (Hilbert.S4Point4M) Kripke.FrameClass.preorder_sobocinski_mckinsey := inferInstance

end Hilbert.S4Point4M.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma S4Point4M.Kripke.preorder_sobocinski_mckinsey : Logic.S4Point4M = FrameClass.preorder_sobocinski_mckinsey.logic := eq_hilbert_logic_frameClass_logic

@[simp]
theorem S4Point4M.proper_extension_of_S4Point3M : Logic.S4Point3M ⊂ Logic.S4Point4M := by
  constructor;
  . rw [S4Point3M.Kripke.preorder_connected_mckinsey, S4Point4M.Kripke.preorder_sobocinski_mckinsey]
    rintro φ hφ F ⟨_, _, _⟩;
    apply hφ;
    refine ⟨inferInstance, inferInstance, inferInstance⟩;
  . suffices ∃ φ, Hilbert.S4Point4M ⊢! φ ∧ ¬Kripke.FrameClass.preorder_connected_mckinsey ⊧ φ by
      rw [S4Point3M.Kripke.preorder_connected_mckinsey];
      tauto;
    use (Axioms.Point4 (.atom 0));
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => x ≤ y⟩, λ w a => w ≠ 1⟩;
      use M, 0;
      constructor
      . refine ⟨?_, ⟨?_⟩, ⟨?_⟩⟩;
        . apply isPreorder_iff _ _ |>.mpr;
          refine ⟨⟨?_⟩, ⟨?_⟩⟩ <;> omega;
        . intro x y z _; omega;
        . intro x; use 2; simp [M];
          constructor <;> omega;
      . suffices ∃ x, (0 : M) ≺ x ∧ ¬x ≺ 1 ∧ (0 : M) ≺ 1 by
          simpa [M, Semantics.Realize, Satisfies];
        use 2;
        omega;

@[simp]
theorem S4Point4M.proper_extension_of_S4Point4 : Logic.S4Point4 ⊂ Logic.S4Point4M := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.S4Point4M ⊢! φ ∧ ¬FrameClass.preorder_sobocinski ⊧ φ by
      rw [S4Point4.Kripke.preorder_sobocinski];
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

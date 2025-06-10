import Foundation.Modal.Kripke.Logic.SobK2
import Foundation.Modal.Kripke.Logic.S4Point3

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open GeachConfluent

abbrev Kripke.FrameClass.preorder_connected_mckinsey : FrameClass := { F | IsPreorder _ F ∧ IsConnected _ F ∧ SatisfiesMcKinseyCondition _ F }

namespace Hilbert.SobK3.Kripke

instance sound : Sound (Hilbert.SobK3) Kripke.FrameClass.preorder_connected_mckinsey := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _⟩ _ (rfl | rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomM_of_satisfiesMcKinseyCondition;
  . exact validate_AxiomPoint3_of_connected;

instance consistent : Entailment.Consistent (Hilbert.SobK3) :=
  consistent_of_sound_frameclass FrameClass.preorder_connected_mckinsey $ by
    use whitepoint;
    refine ⟨inferInstance, inferInstance, inferInstance⟩;

instance canonical : Canonical (Hilbert.SobK3) Kripke.FrameClass.preorder_connected_mckinsey := ⟨by
  apply Set.mem_setOf_eq.mpr;
  refine ⟨?_, ?_, ?_⟩;
  . constructor;
  . infer_instance;
  . infer_instance;
⟩

instance complete : Complete (Hilbert.SobK3) Kripke.FrameClass.preorder_connected_mckinsey := inferInstance

end Hilbert.SobK3.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma SobK3.Kripke.preorder_connected_mckinsey : Logic.SobK3 = FrameClass.preorder_connected_mckinsey.logic := eq_hilbert_logic_frameClass_logic

@[simp]
theorem SobK3.proper_extension_of_SobK2 : Logic.SobK2 ⊂ Logic.SobK3 := by
  constructor;
  . rw [SobK2.Kripke.preorder_confluent_mckinsey, SobK3.Kripke.preorder_connected_mckinsey]
    rintro φ hφ F ⟨_, _, _⟩;
    apply hφ;
    refine ⟨inferInstance, inferInstance, inferInstance⟩;
  . suffices ∃ φ, Hilbert.SobK3 ⊢! φ ∧ ¬Kripke.FrameClass.preorder_confluent_mckinsey ⊧ φ by
      rw [SobK2.Kripke.preorder_confluent_mckinsey];
      tauto;
    use (Axioms.Point3 (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 4, λ x y => x = 0 ∨ y = 3 ∨ x = y⟩,
        λ w a => match a with | 0 => w = 1 ∨ w = 3 | 1 => w = 2 ∨ w = 3 | _ => False
      ⟩;
      use M, 0;
      constructor
      . refine ⟨?_, ⟨?_⟩, ⟨?_⟩⟩;
        . apply isPreorder_iff _ _ |>.mpr;
          refine ⟨⟨?_⟩, ⟨?_⟩⟩ <;> omega;
        . intro x y z ⟨Rxy, Ryz⟩; use 3; simp [M];
        . intro x; use 3; simp [M];
      . suffices
          (∃ x, (0 : M) ≺ x ∧ (∀ (w : M), x ≺ w → w = 1 ∨ w = 3) ∧ x ≠ 2 ∧ x ≠ 3) ∧
          (∃ x, (0 : M) ≺ x ∧ (∀ (w : M), x ≺ w → w = 2 ∨ w = 3) ∧ x ≠ 1 ∧ x ≠ 3) by
          simp [M, Semantics.Realize, Satisfies];
          tauto;
        constructor;
        . use 1; simp only [M]; refine ⟨?_, ?_, ?_, ?_⟩ <;> omega;
        . use 2; simp only [M]; refine ⟨?_, ?_, ?_, ?_⟩ <;> omega;

@[simp]
theorem SobK3.proper_extension_of_S4Point3 : Logic.S4Point3 ⊂ Logic.SobK3 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.SobK3 ⊢! φ ∧ ¬FrameClass.connected_preorder ⊧ φ by
      rw [S4Point3.Kripke.connected_preorder];
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

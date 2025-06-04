import Foundation.Modal.Kripke.Logic.K4
import Foundation.Modal.Kripke.AxiomM
import Foundation.Modal.Kripke.Logic.S4

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open GeachConfluent

abbrev Kripke.FrameClass.preorder_mckinsey : FrameClass := { F | IsPreorder _ F ∧ SatisfiesMcKinseyCondition _ F }

namespace Hilbert.S4Point1

instance Kripke.sound : Sound (Hilbert.S4Point1) (Kripke.FrameClass.preorder_mckinsey) := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomT_of_reflexive;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomM_of_satisfiesMcKinseyCondition;

instance Kripke.consistent : Entailment.Consistent (Hilbert.S4Point1) := consistent_of_sound_frameclass Kripke.FrameClass.preorder_mckinsey $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;

instance Kripke.canonical : Canonical (Hilbert.S4Point1) Kripke.FrameClass.preorder_mckinsey := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor;
  . infer_instance;
  . infer_instance;
⟩

instance Kripke.complete : Complete (Hilbert.S4Point1) Kripke.FrameClass.preorder_mckinsey := inferInstance

end Hilbert.S4Point1

namespace Logic

open Formula
open Entailment
open Kripke

lemma S4Point1.Kripke.preorder_mckinsey : Logic.S4Point1 = FrameClass.preorder_mckinsey.logic := eq_hilbert_logic_frameClass_logic

instance : ProperSublogic Logic.S4 Logic.S4Point1 := ⟨by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.S4Point1 ⊢! φ ∧ ¬FrameClass.preorder ⊧ φ by
      rw [S4.Kripke.preorder];
      tauto;
    use (Axioms.M (.atom 0));
    constructor;
    . exact axiomM!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . apply isPreorder_iff _ _ |>.mpr;
        refine ⟨⟨?_⟩, ⟨?_⟩⟩ <;> simp [M];
      . suffices ∃ x, x ≠ (0 : M.World) by simpa [M, Transitive, Reflexive, Semantics.Realize, Satisfies];
        use 1;
        trivial;
⟩

end Logic

end LO.Modal

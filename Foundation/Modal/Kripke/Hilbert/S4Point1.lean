import Foundation.Modal.Kripke.Hilbert.K4
import Foundation.Modal.Kripke.AxiomM

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

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
  . apply Canonical.satisfiesMcKinseyCondition;
⟩

instance Kripke.complete : Complete (Hilbert.S4Point1) Kripke.FrameClass.preorder_mckinsey := inferInstance

end Hilbert.S4Point1

end LO.Modal

import Foundation.Modal.Kripke.Logic.K4
import Foundation.Modal.Kripke.AxiomM

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.trans_mckinsey : FrameClass := { F | IsTrans _ F ∧ SatisfiesMcKinseyCondition _ F }

namespace Hilbert.K4Point1

instance Kripke.sound : Sound (Hilbert.K4Point1) (Kripke.FrameClass.trans_mckinsey) := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomFour_of_transitive;
  . exact validate_axiomM_of_satisfiesMcKinseyCondition;

instance Kripke.consistent : Entailment.Consistent (Hilbert.K4Point1) := consistent_of_sound_frameclass Kripke.FrameClass.trans_mckinsey $ by
  use whitepoint;
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;

instance Kripke.canonical : Canonical (Hilbert.K4Point1) Kripke.FrameClass.trans_mckinsey := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor;
  . infer_instance;
  . apply Canonical.satisfiesMcKinseyCondition;
⟩

instance Kripke.complete : Complete (Hilbert.K4Point1) Kripke.FrameClass.trans_mckinsey := inferInstance

end Hilbert.K4Point1

lemma Logic.K4Point1.Kripke.trans_mckinsey : Logic.K4Point1 = FrameClass.trans_mckinsey.logic := eq_hilbert_logic_frameClass_logic

end LO.Modal

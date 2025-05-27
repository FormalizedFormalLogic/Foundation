import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.WellKnown

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.serial_trans : FrameClass := { F | IsSerial _ F ∧ IsTrans _ F }

namespace Hilbert.KD4.Kripke

instance sound : Sound (Hilbert.KD4) Kripke.FrameClass.serial_trans := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _⟩ _ (rfl | rfl);
  . exact validate_AxiomD_of_serial;
  . exact validate_AxiomFour_of_transitive;

instance consistent : Entailment.Consistent (Hilbert.KD4) := consistent_of_sound_frameclass
  Kripke.FrameClass.serial_trans $ by
    use whitepoint;
    constructor <;> infer_instance;

instance canonical : Canonical (Hilbert.KD4) Kripke.FrameClass.serial_trans := ⟨by
  apply Set.mem_setOf_eq.mpr;
  constructor <;> infer_instance;
⟩

instance complete : Complete (Hilbert.KD4) Kripke.FrameClass.serial_trans := inferInstance

end Hilbert.KD4.Kripke

lemma Logic.KD4.Kripke.serial_trans : Logic.KD4 = FrameClass.serial_trans.logic := eq_hilbert_logic_frameClass_logic

end LO.Modal

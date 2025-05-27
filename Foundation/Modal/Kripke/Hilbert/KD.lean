import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert.Basic
import Foundation.Modal.Hilbert.WellKnown

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

namespace Kripke.FrameClass

protected abbrev serial : FrameClass := { F | IsSerial _ F.Rel }

end Kripke.FrameClass


namespace Hilbert.KD.Kripke

instance sound : Sound (Hilbert.KD) Kripke.FrameClass.serial :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomK;
    rintro F F_serial φ rfl;
    apply validate_AxiomD_of_serial (ser := F_serial);

instance consistent : Entailment.Consistent (Hilbert.KD) :=
  consistent_of_sound_frameclass FrameClass.serial $ by
    use whitepoint;
    apply Set.mem_setOf_eq.mpr;
    infer_instance;

instance canonical : Canonical (Hilbert.KD) Kripke.FrameClass.serial := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance complete : Complete (Hilbert.KD) Kripke.FrameClass.serial := inferInstance

end Hilbert.KD.Kripke

lemma Logic.KD.Kripke.serial : Logic.KD = FrameClass.serial.logic := eq_hilbert_logic_frameClass_logic

end LO.Modal

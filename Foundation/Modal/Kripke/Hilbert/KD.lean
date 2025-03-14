import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

namespace Kripke.FrameClass

protected abbrev serial : FrameClass := { F | Serial F }

namespace serial

lemma isMultiGeachean : FrameClass.serial = FrameClass.multiGeachean {⟨0, 0, 1, 1⟩} := by
  ext F;
  simp [Geachean.serial_def, MultiGeachean]

@[simp]
lemma nonempty : FrameClass.serial.Nonempty := by simp [isMultiGeachean]

lemma validates_AxiomD : FrameClass.serial.ValidatesFormula (Axioms.D (.atom 0)) := by
  rintro F F_serial _ rfl;
  apply validate_AxiomD_of_serial $ by assumption

lemma validates_HilbertKD : FrameClass.serial.Validates Hilbert.KD.axioms := by
  apply FrameClass.Validates.withAxiomK;
  apply validates_AxiomD;

end serial

end Kripke.FrameClass


namespace Hilbert.KD

instance Kripke.sound : Sound (Hilbert.KD) Kripke.FrameClass.serial :=
  instSound_of_validates_axioms FrameClass.serial.validates_HilbertKD

instance Kripke.consistent : Entailment.Consistent (Hilbert.KD) :=
  consistent_of_sound_frameclass FrameClass.serial (by simp)

instance Kripke.canonical : Canonical (Hilbert.KD) Kripke.FrameClass.serial := ⟨Canonical.serial⟩

instance Kripke.complete : Complete (Hilbert.KD) Kripke.FrameClass.serial := inferInstance

end Hilbert.KD

end LO.Modal

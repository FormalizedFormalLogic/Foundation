import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.serial_trans : FrameClass := { F | Serial F ∧ Transitive F }

namespace Kripke.FrameClass.serial_trans

lemma isMultiGeachean : FrameClass.serial_trans = FrameClass.multiGeachean {⟨0, 0, 1, 1⟩, ⟨0, 2, 1, 0⟩} := by
  ext F;
  simp [Geachean.serial_def, Geachean.transitive_def, MultiGeachean]

@[simp]
lemma nonempty : FrameClass.serial_trans.Nonempty := by simp [isMultiGeachean]

lemma validates_HilbertKD4 : Kripke.FrameClass.serial_trans.Validates Hilbert.KD4.axioms := by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨F_serial, F_trans⟩ φ (rfl | rfl);
  . exact validate_AxiomD_of_serial $ by assumption;
  . exact validate_AxiomFour_of_transitive $ by assumption;

end Kripke.FrameClass.serial_trans



namespace Hilbert.KD4

instance Kripke.sound : Sound (Hilbert.KD4) Kripke.FrameClass.serial_trans :=
  instSound_of_validates_axioms Kripke.FrameClass.serial_trans.validates_HilbertKD4

instance Kripke.consistent : Entailment.Consistent (Hilbert.KD4) :=
  consistent_of_sound_frameclass Kripke.FrameClass.serial_trans (by simp)

instance Kripke.canonical : Canonical (Hilbert.KD4) Kripke.FrameClass.serial_trans := ⟨⟨Canonical.serial, Canonical.transitive⟩⟩

instance Kripke.complete : Complete (Hilbert.KD4) Kripke.FrameClass.serial_trans := inferInstance


end Hilbert.KD4

end LO.Modal

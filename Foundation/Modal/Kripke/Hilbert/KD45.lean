import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.serial_trans_eucl : FrameClass := { F | Serial F ∧ Transitive F ∧ Euclidean F }

namespace Kripke.FrameClass.serial_trans_eucl

lemma isMultiGeachean : FrameClass.serial_trans_eucl = FrameClass.multiGeachean {⟨0, 0, 1, 1⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩} := by
  ext F;
  simp [Geachean.serial_def, Geachean.transitive_def, Geachean.euclidean_def, MultiGeachean]

@[simp]
lemma nonempty : FrameClass.serial_trans_eucl.Nonempty := by simp [isMultiGeachean]

lemma validates_HilbertKD45 : Kripke.FrameClass.serial_trans_eucl.Validates Hilbert.KD45.axioms := by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨F_serial, F_trans, F_eucl⟩ φ (rfl | rfl | rfl);
  . exact validate_AxiomD_of_serial $ by assumption;
  . exact validate_AxiomFour_of_transitive $ by assumption;
  . exact validate_AxiomFive_of_euclidean $ by assumption;

end Kripke.FrameClass.serial_trans_eucl



namespace Hilbert.KD45

instance Kripke.sound : Sound (Hilbert.KD45) Kripke.FrameClass.serial_trans_eucl :=
  instSound_of_validates_axioms Kripke.FrameClass.serial_trans_eucl.validates_HilbertKD45

instance Kripke.consistent : Entailment.Consistent (Hilbert.KD45) :=
  consistent_of_sound_frameclass Kripke.FrameClass.serial_trans_eucl (by simp)

instance Kripke.canonical : Canonical (Hilbert.KD45) Kripke.FrameClass.serial_trans_eucl := ⟨⟨Canonical.serial, Canonical.transitive, Canonical.euclidean⟩⟩

instance Kripke.complete : Complete (Hilbert.KD45) Kripke.FrameClass.serial_trans_eucl := inferInstance


end Hilbert.KD45

end LO.Modal

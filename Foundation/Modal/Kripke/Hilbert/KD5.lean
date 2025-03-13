import Foundation.Modal.Kripke.Hilbert.Geach
namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.serial_eucl : FrameClass := { F | Serial F ∧ Euclidean F }

namespace Kripke.FrameClass.serial_eucl

lemma isMultiGeachean : FrameClass.serial_eucl = FrameClass.multiGeachean {⟨0, 0, 1, 1⟩, ⟨1, 1, 0, 1⟩} := by
  ext F;
  simp [Geachean.serial_def, Geachean.euclidean_def, MultiGeachean]

@[simp]
lemma nonempty : FrameClass.serial_eucl.Nonempty := by simp [isMultiGeachean]

lemma validates_HilbertKD5 : Kripke.FrameClass.serial_eucl.Validates Hilbert.KD5.axioms := by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨F_serial, F_eucl⟩ φ (rfl | rfl);
  . exact validate_AxiomD_of_serial $ by assumption;
  . exact validate_AxiomFive_of_euclidean $ by assumption;

end Kripke.FrameClass.serial_eucl



namespace Hilbert.KD5

instance Kripke.sound : Sound (Hilbert.KD5) Kripke.FrameClass.serial_eucl :=
  instSound_of_validates_axioms Kripke.FrameClass.serial_eucl.validates_HilbertKD5

instance Kripke.consistent : Entailment.Consistent (Hilbert.KD5) :=
  consistent_of_sound_frameclass Kripke.FrameClass.serial_eucl (by simp)

instance Kripke.canonical : Canonical (Hilbert.KD5) Kripke.FrameClass.serial_eucl := ⟨⟨Canonical.serial, Canonical.euclidean⟩⟩

instance Kripke.complete : Complete (Hilbert.KD5) Kripke.FrameClass.serial_eucl := inferInstance


end Hilbert.KD5

end LO.Modal

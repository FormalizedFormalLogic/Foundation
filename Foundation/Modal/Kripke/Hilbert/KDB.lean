import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.serial_symm : FrameClass := { F | Serial F ∧ Symmetric F }

namespace Kripke.FrameClass.serial_symm

lemma isMultiGeachean : FrameClass.serial_symm = FrameClass.multiGeachean {⟨0, 0, 1, 1⟩, ⟨0, 1, 0, 1⟩} := by
  ext F;
  simp [Geachean.serial_def, Geachean.symmetric_def, MultiGeachean]

@[simp]
lemma nonempty : FrameClass.serial_symm.Nonempty := by simp [isMultiGeachean]

lemma validates_HilbertKDB : Kripke.FrameClass.serial_symm.Validates Hilbert.KDB.axioms := by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨F_serial, F_eucl⟩ φ (rfl | rfl);
  . exact validate_AxiomD_of_serial $ by assumption;
  . exact validate_AxiomB_of_symmetric $ by assumption;

end Kripke.FrameClass.serial_symm



namespace Hilbert.KDB

instance Kripke.sound : Sound (Hilbert.KDB) Kripke.FrameClass.serial_symm :=
  instSound_of_validates_axioms Kripke.FrameClass.serial_symm.validates_HilbertKDB

instance Kripke.consistent : Entailment.Consistent (Hilbert.KDB) :=
  consistent_of_sound_frameclass Kripke.FrameClass.serial_symm (by simp)

instance Kripke.canonical : Canonical (Hilbert.KDB) Kripke.FrameClass.serial_symm := ⟨⟨Canonical.serial, Canonical.symmetric⟩⟩

instance Kripke.complete : Complete (Hilbert.KDB) Kripke.FrameClass.serial_symm := inferInstance

end Hilbert.KDB

end LO.Modal

import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.symm_trans : FrameClass := { F | Symmetric F ∧ Transitive F }

namespace Kripke.FrameClass.symm_trans

lemma isMultiGeachean : FrameClass.symm_trans = FrameClass.multiGeachean {⟨0, 1, 0, 1⟩, ⟨0, 2, 1, 0⟩} := by
  ext F;
  simp [Geachean.transitive_def, Geachean.symmetric_def, MultiGeachean]

@[simp]
lemma nonempty : FrameClass.symm_trans.Nonempty := by simp [isMultiGeachean]

lemma validates_HilbertKB4 : Kripke.FrameClass.symm_trans.Validates Hilbert.KB4.axioms := by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨F_symm, F_trans⟩ φ (rfl | rfl);
  . exact validate_AxiomB_of_symmetric $ by assumption;
  . exact validate_AxiomFour_of_transitive $ by assumption;

end Kripke.FrameClass.symm_trans



namespace Hilbert.KB4

instance Kripke.sound : Sound (Hilbert.KB4) Kripke.FrameClass.symm_trans :=
  instSound_of_validates_axioms Kripke.FrameClass.symm_trans.validates_HilbertKB4

instance Kripke.consistent : Entailment.Consistent (Hilbert.KB4) :=
  consistent_of_sound_frameclass Kripke.FrameClass.symm_trans (by simp)

instance Kripke.canonical : Canonical (Hilbert.KB4) Kripke.FrameClass.symm_trans := ⟨⟨Canonical.symmetric, Canonical.transitive⟩⟩

instance Kripke.complete : Complete (Hilbert.KB4) Kripke.FrameClass.symm_trans := inferInstance


end Hilbert.KB4

end LO.Modal

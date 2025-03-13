import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

abbrev Kripke.FrameClass.symm_eucl : FrameClass := { F | Symmetric F ∧ Euclidean F }

namespace Kripke.FrameClass.symm_eucl

lemma isMultiGeachean : FrameClass.symm_eucl = FrameClass.multiGeachean {⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩} := by
  ext F;
  simp [Geachean.euclidean_def, Geachean.symmetric_def, MultiGeachean]

@[simp]
lemma nonempty : FrameClass.symm_eucl.Nonempty := by simp [isMultiGeachean]

lemma validates_HilbertKB5 : Kripke.FrameClass.symm_eucl.Validates Hilbert.KB5.axioms := by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨F_symm, F_eucl⟩ φ (rfl | rfl);
  . exact validate_AxiomB_of_symmetric $ by assumption;
  . exact validate_AxiomFive_of_euclidean $ by assumption;

end Kripke.FrameClass.symm_eucl



namespace Hilbert.KB5

instance Kripke.sound : Sound (Hilbert.KB5) Kripke.FrameClass.symm_eucl :=
  instSound_of_validates_axioms Kripke.FrameClass.symm_eucl.validates_HilbertKB5

instance Kripke.consistent : Entailment.Consistent (Hilbert.KB5) :=
  consistent_of_sound_frameclass Kripke.FrameClass.symm_eucl (by simp)

instance Kripke.canonical : Canonical (Hilbert.KB5) Kripke.FrameClass.symm_eucl := ⟨⟨Canonical.symmetric, Canonical.euclidean⟩⟩

instance Kripke.complete : Complete (Hilbert.KB5) Kripke.FrameClass.symm_eucl := inferInstance


end Hilbert.KB5

end LO.Modal

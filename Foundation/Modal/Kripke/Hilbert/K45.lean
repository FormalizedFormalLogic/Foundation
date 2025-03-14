import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

protected abbrev Kripke.FrameClass.trans_eucl : FrameClass := { F | Transitive F ∧ Euclidean F }

namespace Kripke.FrameClass.trans_eucl

lemma isMultiGeachean : FrameClass.trans_eucl = FrameClass.multiGeachean {⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩} := by
  ext F;
  simp [Geachean.transitive_def, Geachean.euclidean_def, MultiGeachean]

@[simp]
lemma nonempty : FrameClass.trans_eucl.Nonempty := by simp [isMultiGeachean]

lemma validates_HilbertK45 : Kripke.FrameClass.trans_eucl.Validates Hilbert.K45.axioms := by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨F_trans, F_eucl⟩ φ (rfl | rfl);
  . exact validate_AxiomFour_of_transitive $ by assumption;
  . exact validate_AxiomFive_of_euclidean $ by assumption;

end Kripke.FrameClass.trans_eucl


namespace Hilbert.K45

instance Kripke.sound : Sound (Hilbert.K45) FrameClass.trans_eucl :=
  instSound_of_validates_axioms Kripke.FrameClass.trans_eucl.validates_HilbertK45

instance Kripke.consistent : Entailment.Consistent (Hilbert.K45) :=
  consistent_of_sound_frameclass Kripke.FrameClass.trans_eucl (by simp)

instance Kripke.canonical : Canonical (Hilbert.K45) FrameClass.trans_eucl :=
  ⟨⟨Canonical.transitive, Canonical.euclidean⟩⟩

instance Kripke.complete : Complete (Hilbert.K45) FrameClass.trans_eucl := inferInstance

end Hilbert.K45

end LO.Modal

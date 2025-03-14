import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open Geachean

namespace Kripke.FrameClass

abbrev eucl : FrameClass := { F | Euclidean F }
-- abbrev Kripke.EuclideanFiniteFrameClass: FrameClass := { F | Euclidean F.Rel }

namespace eucl

lemma isMultiGeachean : FrameClass.eucl = FrameClass.multiGeachean {⟨1, 1, 0, 1⟩} := by
  ext F;
  simp [Geachean.euclidean_def, MultiGeachean]

@[simp]
lemma nonempty : FrameClass.eucl.Nonempty := by simp [eucl.isMultiGeachean]

lemma validates_AxiomFive : FrameClass.eucl.ValidatesFormula (Axioms.Five (.atom 0)) := by
  rintro F F_eucl _ rfl;
  apply validate_AxiomFive_of_euclidean $ by assumption

lemma validates_HilbertK5 : FrameClass.eucl.Validates Hilbert.K5.axioms := by
  apply FrameClass.Validates.withAxiomK;
  apply validates_AxiomFive;

end eucl

end Kripke.FrameClass


namespace Hilbert.K5.Kripke

instance sound : Sound (Hilbert.K5) Kripke.FrameClass.eucl :=
  instSound_of_validates_axioms Kripke.FrameClass.eucl.validates_HilbertK5

instance consistent : Entailment.Consistent (Hilbert.K5) :=
  consistent_of_sound_frameclass Kripke.FrameClass.eucl (by simp)

instance canonical : Canonical (Hilbert.K5) Kripke.FrameClass.eucl := ⟨Canonical.euclidean⟩

instance complete : Complete (Hilbert.K5) Kripke.FrameClass.eucl := inferInstance

end Hilbert.K5.Kripke

end LO.Modal

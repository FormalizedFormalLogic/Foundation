import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.EuclideanFrameClass : FrameClass := { F | Euclidean F }
-- abbrev Kripke.EuclideanFiniteFrameClass : FiniteFrameClass := { F | Euclidean F.Rel }

namespace Hilbert.K5

instance Kripke.sound : Sound (Hilbert.K5) (Kripke.EuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨1, 1, 0, 1⟩});
  exact eq_Geach;
  . unfold EuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.euclidean_def];

instance Kripke.consistent : Entailment.Consistent (Hilbert.K5) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨1, 1, 0, 1⟩});
  exact eq_Geach;

instance Kripke.canonical : Canonical (Hilbert.K5) (Kripke.EuclideanFrameClass) := ⟨Canonical.euclidean⟩

instance Kripke.complete : Complete (Hilbert.K5) (Kripke.EuclideanFrameClass) := inferInstance

end Hilbert.K5

end LO.Modal

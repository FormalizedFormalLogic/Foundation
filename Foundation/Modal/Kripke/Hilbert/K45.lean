import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.TransitiveEuclideanFrameClass : FrameClass := { F | Transitive F ∧ Euclidean F }

namespace Hilbert.K45

instance Kripke.sound : Sound (Hilbert.K45) (Kripke.TransitiveEuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩});
  . exact eq_Geach;
  . unfold TransitiveEuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.euclidean_def, Geachean.transitive_def];

instance Kripke.consistent : Entailment.Consistent (Hilbert.K45) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩});
  exact eq_Geach;

instance Kripke.complete : Complete (Hilbert.K45) (Kripke.TransitiveEuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩});
  . exact eq_Geach;
  . unfold TransitiveEuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.euclidean_def, Geachean.transitive_def];

end Hilbert.K45

end LO.Modal

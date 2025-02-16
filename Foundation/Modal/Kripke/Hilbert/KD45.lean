import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.SerialTransitiveEuclideanFrameClass : FrameClass := { F | Serial F ∧ Transitive F ∧ Euclidean F }

namespace Hilbert.KD45

instance Kripke.sound : Sound (Hilbert.KD45) (Kripke.SerialTransitiveEuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 1⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩});
  . exact eq_Geach;
  . unfold SerialTransitiveEuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.serial_def, Geachean.euclidean_def, Geachean.transitive_def];

instance Kripke.consistent : Entailment.Consistent (Hilbert.KD45) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 1⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩});
  exact eq_Geach;

instance Kripke.complete : Complete (Hilbert.KD45) (Kripke.SerialTransitiveEuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 1⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩});
  . exact eq_Geach;
  . unfold SerialTransitiveEuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.serial_def, Geachean.euclidean_def, Geachean.transitive_def];

end Hilbert.KD45

end LO.Modal

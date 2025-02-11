import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.SerialEuclideanFrameClass : FrameClass := { F | Serial F ∧ Euclidean F }

namespace Hilbert.KD5

instance Kripke.sound : Sound (Hilbert.KD5) (Kripke.SerialEuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 1⟩, ⟨1, 1, 0, 1⟩});
  . exact eq_Geach;
  . unfold SerialEuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.serial_def, Geachean.euclidean_def];

instance Kripke.consistent : Entailment.Consistent (Hilbert.KD5) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 1⟩, ⟨1, 1, 0, 1⟩});
  exact eq_Geach;

instance Kripke.complete : Complete (Hilbert.KD5) (Kripke.SerialEuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 1⟩, ⟨1, 1, 0, 1⟩});
  . exact eq_Geach;
  . unfold SerialEuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.serial_def, Geachean.euclidean_def];

end Hilbert.KD5

end LO.Modal

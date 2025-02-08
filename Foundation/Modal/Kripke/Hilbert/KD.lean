import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.SerialFrameClass : FrameClass := { F | Serial F }

namespace Hilbert.KD

instance Kripke.sound : Sound (Hilbert.KD) (Kripke.SerialFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 1⟩});
  . exact eq_Geach;
  . unfold SerialFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.serial_def];

instance Kripke.consistent : System.Consistent (Hilbert.KD) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 1⟩});
  exact eq_Geach;

instance Kripke.complete : Complete (Hilbert.KD) (Kripke.SerialFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 1⟩});
  . exact eq_Geach;
  . unfold SerialFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.serial_def];

end Hilbert.KD

end LO.Modal

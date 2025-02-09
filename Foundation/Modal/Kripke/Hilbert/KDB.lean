import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.SerialSymmetricFrameClass : FrameClass := { F | Serial F ∧ Symmetric F }

namespace Hilbert.KDB

instance Kripke.sound : Sound (Hilbert.KDB) (Kripke.SerialSymmetricFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 1⟩, ⟨0, 1, 0, 1⟩});
  . exact eq_Geach;
  . unfold SerialSymmetricFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.serial_def, Geachean.symmetric_def];

instance Kripke.consistent : System.Consistent (Hilbert.KDB) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 1⟩, ⟨0, 1, 0, 1⟩});
  exact eq_Geach;

instance Kripke.complete : Complete (Hilbert.KDB) (Kripke.SerialSymmetricFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 1⟩, ⟨0, 1, 0, 1⟩});
  . exact eq_Geach;
  . unfold SerialSymmetricFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.serial_def, Geachean.symmetric_def];

end Hilbert.KDB

end LO.Modal

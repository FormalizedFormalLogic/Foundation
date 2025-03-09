import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.FrameClass.serial : FrameClass := { F | Serial F }

namespace Hilbert.KD

instance Kripke.sound : Sound (Hilbert.KD) Kripke.FrameClass.serial := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 1⟩});
  . exact eq_Geach;
  . unfold Kripke.FrameClass.serial FrameClass.multiGeachean MultiGeachean;
    simp [Geachean.serial_def];

instance Kripke.consistent : Entailment.Consistent (Hilbert.KD) := by
  convert Hilbert.Geach.Kripke.consistent (G := {⟨0, 0, 1, 1⟩});
  exact eq_Geach;

instance Kripke.canonical : Canonical (Hilbert.KD) Kripke.FrameClass.serial := ⟨Canonical.serial⟩

instance Kripke.complete : Complete (Hilbert.KD) Kripke.FrameClass.serial := inferInstance

end Hilbert.KD

end LO.Modal

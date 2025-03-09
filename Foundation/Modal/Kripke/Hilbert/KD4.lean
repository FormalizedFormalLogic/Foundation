import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.FrameClass.serial_trans : FrameClass := { F | Serial F ∧ Transitive F }

namespace Hilbert.KD4

instance Kripke.sound : Sound (Hilbert.KD4) Kripke.FrameClass.serial_trans := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 1⟩, ⟨0, 2, 1, 0⟩});
  . exact eq_Geach;
  . unfold Kripke.FrameClass.serial_trans FrameClass.multiGeachean MultiGeachean;
    simp [Geachean.serial_def, Geachean.transitive_def];

instance Kripke.consistent : Entailment.Consistent (Hilbert.KD4) := by
  convert Hilbert.Geach.Kripke.consistent (G := {⟨0, 0, 1, 1⟩, ⟨0, 2, 1, 0⟩});
  exact eq_Geach;

instance Kripke.canonical : Canonical (Hilbert.KD4) Kripke.FrameClass.serial_trans := ⟨⟨Canonical.serial, Canonical.transitive⟩⟩

instance Kripke.complete : Complete (Hilbert.KD4) Kripke.FrameClass.serial_trans := inferInstance

end Hilbert.KD4

end LO.Modal

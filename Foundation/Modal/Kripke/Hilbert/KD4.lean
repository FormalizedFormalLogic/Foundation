import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.SerialTransitiveFrameClass : FrameClass := { F | Serial F ∧ Transitive F }

namespace Hilbert.KD4

instance Kripke.sound : Sound (Hilbert.KD4) (Kripke.SerialTransitiveFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 1⟩, ⟨0, 2, 1, 0⟩});
  . exact eq_Geach;
  . unfold SerialTransitiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.serial_def, Geachean.transitive_def];

instance Kripke.consistent : Entailment.Consistent (Hilbert.KD4) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 1⟩, ⟨0, 2, 1, 0⟩});
  exact eq_Geach;

instance Kripke.canonical : Canonical (Hilbert.KD4) (SerialTransitiveFrameClass) := ⟨⟨Canonical.serial, Canonical.transitive⟩⟩

instance Kripke.complete : Complete (Hilbert.KD4) (SerialTransitiveFrameClass) := inferInstance

end Hilbert.KD4

end LO.Modal

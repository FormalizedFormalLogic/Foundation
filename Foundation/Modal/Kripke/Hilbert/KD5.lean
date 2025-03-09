import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.FrameClass.serial_eucl : FrameClass := { F | Serial F ∧ Euclidean F }

namespace Hilbert.KD5

instance Kripke.sound : Sound (Hilbert.KD5) Kripke.FrameClass.serial_eucl := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 1⟩, ⟨1, 1, 0, 1⟩});
  . exact eq_Geach;
  . unfold Kripke.FrameClass.serial_eucl FrameClass.multiGeachean MultiGeachean;
    simp [Geachean.serial_def, Geachean.euclidean_def];

instance Kripke.consistent : Entailment.Consistent (Hilbert.KD5) := by
  convert Hilbert.Geach.Kripke.consistent (G := {⟨0, 0, 1, 1⟩, ⟨1, 1, 0, 1⟩});
  exact eq_Geach;

instance Kripke.canonical : Canonical (Hilbert.KD5) Kripke.FrameClass.serial_eucl := ⟨⟨Canonical.serial, Canonical.euclidean⟩⟩

instance Kripke.complete : Complete (Hilbert.KD5) Kripke.FrameClass.serial_eucl := inferInstance

end Hilbert.KD5

end LO.Modal

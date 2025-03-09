import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.FrameClass.serial_trans_eucl : FrameClass := { F | Serial F ∧ Transitive F ∧ Euclidean F }

namespace Hilbert.KD45

instance Kripke.sound : Sound (Hilbert.KD45) Kripke.FrameClass.serial_trans_eucl := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 1⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩});
  . exact eq_Geach;
  . unfold Kripke.FrameClass.serial_trans_eucl FrameClass.multiGeachean MultiGeachean;
    simp [Geachean.serial_def, Geachean.euclidean_def, Geachean.transitive_def];

instance Kripke.consistent : Entailment.Consistent (Hilbert.KD45) := by
  convert Hilbert.Geach.Kripke.consistent (G := {⟨0, 0, 1, 1⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩});
  exact eq_Geach;

instance Kripke.canonical : Canonical (Hilbert.KD45) Kripke.FrameClass.serial_trans_eucl := ⟨⟨Canonical.serial, Canonical.transitive, Canonical.euclidean⟩⟩

instance Kripke.complete : Complete (Hilbert.KD45) Kripke.FrameClass.serial_trans_eucl := inferInstance

end Hilbert.KD45

end LO.Modal

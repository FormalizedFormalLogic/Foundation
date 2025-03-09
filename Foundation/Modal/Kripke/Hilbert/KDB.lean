import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.FrameClass.serial_symm : FrameClass := { F | Serial F ∧ Symmetric F }

namespace Hilbert.KDB

instance Kripke.sound : Sound (Hilbert.KDB) Kripke.FrameClass.serial_symm := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 1⟩, ⟨0, 1, 0, 1⟩});
  . exact eq_Geach;
  . unfold Kripke.FrameClass.serial_symm FrameClass.multiGeachean MultiGeachean;
    simp [Geachean.serial_def, Geachean.symmetric_def];

instance Kripke.consistent : Entailment.Consistent (Hilbert.KDB) := by
  convert Hilbert.Geach.Kripke.consistent (G := {⟨0, 0, 1, 1⟩, ⟨0, 1, 0, 1⟩});
  exact eq_Geach;

instance Kripke.canonical : Canonical (Hilbert.KDB) Kripke.FrameClass.serial_symm := ⟨⟨Canonical.serial, Canonical.symmetric⟩⟩

instance Kripke.complete : Complete (Hilbert.KDB) Kripke.FrameClass.serial_symm := inferInstance

end Hilbert.KDB

end LO.Modal

import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.FrameClass.symm : FrameClass := { F | Symmetric F }

namespace Hilbert.KB

instance Kripke.sound : Sound (Hilbert.KB) Kripke.FrameClass.symm := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 1, 0, 1⟩});
  . exact eq_Geach;
  . unfold Kripke.FrameClass.symm FrameClass.multiGeachean MultiGeachean;
    simp [Geachean.symmetric_def];

instance Kripke.consistent : Entailment.Consistent (Hilbert.KB) := by
  convert Hilbert.Geach.Kripke.consistent (G := {⟨0, 1, 0, 1⟩});
  exact eq_Geach;

instance Kripke.canonical : Canonical (Hilbert.KB) Kripke.FrameClass.symm := ⟨Canonical.symmetric⟩

instance Kripke.complete : Complete (Hilbert.KB) Kripke.FrameClass.symm := inferInstance

end Hilbert.KB

end LO.Modal

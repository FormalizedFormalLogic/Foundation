import Foundation.Modal.Kripke2.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.ReflexiveFrameClass : FrameClass := { F | Reflexive F }

namespace Hilbert.KT

instance Kripke.consistent : System.Consistent (Hilbert.KT) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 0⟩});
  exact eq_Geach;

instance Kripke.complete : Complete (Hilbert.KT) (Kripke.ReflexiveFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 0⟩});
  . exact eq_Geach;
  . unfold ReflexiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def];

end Hilbert.KT

end LO.Modal

import Foundation.Modal.Kripke2.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.ReflexiveTransitiveFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F }

namespace Hilbert.S4

instance Kripke.Consistent : System.Consistent (Hilbert.S4) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩});
  exact eq_Geach;

instance Kripke.Complete : Complete (Hilbert.S4) (Kripke.ReflexiveTransitiveFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩});
  . exact eq_Geach;
  . unfold ReflexiveTransitiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.transitive_def];

end Hilbert.S4

end LO.Modal

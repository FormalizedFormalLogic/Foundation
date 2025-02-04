import Foundation.Modal.Kripke2.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.ReflexiveTransitiveConfluentFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Confluent F  }

namespace Hilbert.S4Dot2

instance Kripke.Consistent : System.Consistent (Hilbert.S4Dot2) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩});
  exact eq_Geach;

instance Kripke.Complete : Complete (Hilbert.S4Dot2) (ReflexiveTransitiveConfluentFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩});
  . exact eq_Geach;
  . unfold ReflexiveTransitiveConfluentFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.transitive_def, Geachean.confluent_def];

end Hilbert.S4Dot2

end LO.Modal

import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.FrameClass.confluent_preorder : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Confluent F  }

namespace Hilbert.S4Point2

instance Kripke.sound : Sound (Hilbert.S4Point2) Kripke.FrameClass.confluent_preorder := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩});
  . exact eq_Geach;
  . unfold Kripke.FrameClass.confluent_preorder FrameClass.multiGeachean MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.transitive_def, Geachean.confluent_def];

instance Kripke.consistent : Entailment.Consistent (Hilbert.S4Point2) := by
  convert Hilbert.Geach.Kripke.consistent (G := {⟨0, 0, 1, 0⟩, ⟨0, 2, 1, 0⟩, ⟨1, 1, 1, 1⟩});
  exact eq_Geach;

instance Kripke.canonical : Canonical (Hilbert.S4Point2) Kripke.FrameClass.confluent_preorder := ⟨⟨Canonical.reflexive, Canonical.transitive, Canonical.confluent⟩⟩

instance Kripke.complete : Complete (Hilbert.S4Point2) Kripke.FrameClass.confluent_preorder := inferInstance

end Hilbert.S4Point2

end LO.Modal

import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

protected abbrev Kripke.FrameClass.trans_eucl : FrameClass := { F | Transitive F ∧ Euclidean F }

namespace Hilbert.K45

instance Kripke.sound : Sound (Hilbert.K45) FrameClass.trans_eucl := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩});
  . exact eq_Geach;
  . unfold FrameClass.trans_eucl FrameClass.multiGeachean MultiGeachean;
    simp [Geachean.euclidean_def, Geachean.transitive_def];

instance Kripke.consistent : Entailment.Consistent (Hilbert.K45) := by
  convert Hilbert.Geach.Kripke.consistent (G := {⟨0, 2, 1, 0⟩, ⟨1, 1, 0, 1⟩});
  exact eq_Geach;

instance Kripke.canonical : Canonical (Hilbert.K45) FrameClass.trans_eucl :=
  ⟨⟨Canonical.transitive, Canonical.euclidean⟩⟩

instance Kripke.complete : Complete (Hilbert.K45) FrameClass.trans_eucl := inferInstance

end Hilbert.K45

end LO.Modal

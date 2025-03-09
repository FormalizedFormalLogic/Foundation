import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.FrameClass.symm_eucl : FrameClass := { F | Symmetric F ∧ Euclidean F }

namespace Hilbert.KB5

instance Kripke.sound : Sound (Hilbert.KB5) Kripke.FrameClass.symm_eucl := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩});
  . exact eq_Geach;
  . unfold Kripke.FrameClass.symm_eucl FrameClass.multiGeachean MultiGeachean;
    simp [Geachean.symmetric_def, Geachean.euclidean_def];

instance Kripke.consistent : Entailment.Consistent (Hilbert.KB5) := by
  convert Hilbert.Geach.Kripke.consistent (G := {⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩});
  exact eq_Geach;

instance Kripke.canonical : Canonical (Hilbert.KB5) Kripke.FrameClass.symm_eucl := ⟨⟨Canonical.symmetric, Canonical.euclidean⟩⟩

instance Kripke.complete : Complete (Hilbert.KB5) Kripke.FrameClass.symm_eucl := inferInstance

end Hilbert.KB5

end LO.Modal

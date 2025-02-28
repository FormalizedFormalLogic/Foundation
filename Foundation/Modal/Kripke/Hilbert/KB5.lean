import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.SymmetricEuclideanFrameClass : FrameClass := { F | Symmetric F ∧ Euclidean F }

namespace Hilbert.KB5

instance Kripke.sound : Sound (Hilbert.KB5) (Kripke.SymmetricEuclideanFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩});
  . exact eq_Geach;
  . unfold SymmetricEuclideanFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.symmetric_def, Geachean.euclidean_def];

instance Kripke.consistent : Entailment.Consistent (Hilbert.KB5) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 1, 0, 1⟩, ⟨1, 1, 0, 1⟩});
  exact eq_Geach;

instance Kripke.canonical : Canonical (Hilbert.KB5) (SymmetricEuclideanFrameClass) := ⟨⟨Canonical.symmetric, Canonical.euclidean⟩⟩

instance Kripke.complete : Complete (Hilbert.KB5) (SymmetricEuclideanFrameClass) := inferInstance

end Hilbert.KB5

end LO.Modal

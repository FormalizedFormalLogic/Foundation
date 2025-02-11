import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.SymmetricTransitiveFrameClass : FrameClass := { F | Symmetric F ∧ Transitive F }

namespace Hilbert.KB4

instance Kripke.sound : Sound (Hilbert.KB4) (Kripke.SymmetricTransitiveFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 1, 0, 1⟩, ⟨0, 2, 1, 0⟩});
  . exact eq_Geach;
  . unfold SymmetricTransitiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.symmetric_def, Geachean.transitive_def];

instance Kripke.consistent : Entailment.Consistent (Hilbert.KB4) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 1, 0, 1⟩, ⟨0, 2, 1, 0⟩});
  exact eq_Geach;

instance Kripke.complete : Complete (Hilbert.KB4) (Kripke.SymmetricTransitiveFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 1, 0, 1⟩, ⟨0, 2, 1, 0⟩});
  . exact eq_Geach;
  . unfold SymmetricTransitiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.symmetric_def, Geachean.transitive_def];

end Hilbert.KB4

end LO.Modal

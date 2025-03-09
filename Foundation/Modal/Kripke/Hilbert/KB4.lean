import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.FrameClass.symm_trans : FrameClass := { F | Symmetric F ∧ Transitive F }

namespace Hilbert.KB4

instance Kripke.sound : Sound (Hilbert.KB4) Kripke.FrameClass.symm_trans := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 1, 0, 1⟩, ⟨0, 2, 1, 0⟩});
  . exact eq_Geach;
  . unfold Kripke.FrameClass.symm_trans FrameClass.multiGeachean MultiGeachean;
    simp [Geachean.symmetric_def, Geachean.transitive_def];

instance Kripke.consistent : Entailment.Consistent (Hilbert.KB4) := by
  convert Hilbert.Geach.Kripke.consistent (G := {⟨0, 1, 0, 1⟩, ⟨0, 2, 1, 0⟩});
  exact eq_Geach;

instance Kripke.canonical : Canonical (Hilbert.KB4) Kripke.FrameClass.symm_trans := ⟨⟨Canonical.symmetric, Canonical.transitive⟩⟩

instance Kripke.complete : Complete (Hilbert.KB4) Kripke.FrameClass.symm_trans := inferInstance


end Hilbert.KB4

end LO.Modal

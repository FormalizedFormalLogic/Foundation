import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.SymmetricFrameClass : FrameClass := { F | Symmetric F }

namespace Hilbert.KB

instance Kripke.sound : Sound (Hilbert.KB) (Kripke.SymmetricFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 1, 0, 1⟩});
  . exact eq_Geach;
  . unfold SymmetricFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.symmetric_def];

instance Kripke.consistent : Entailment.Consistent (Hilbert.KB) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 1, 0, 1⟩});
  exact eq_Geach;

instance Kripke.complete : Complete (Hilbert.KB) (Kripke.SymmetricFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 1, 0, 1⟩});
  . exact eq_Geach;
  . unfold SymmetricFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.symmetric_def];

end Hilbert.KB

end LO.Modal

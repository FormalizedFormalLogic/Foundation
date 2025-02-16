import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.CoreflexiveFrameClass : FrameClass := { F | Coreflexive F }

namespace Hilbert.KTc

instance Kripke.sound : Sound (Hilbert.KTc) (Kripke.CoreflexiveFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 1, 0, 0⟩});
  exact eq_Geach;
  . unfold CoreflexiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.coreflexive_def];

instance Kripke.consistent : Entailment.Consistent (Hilbert.KTc) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 1, 0, 0⟩});
  exact eq_Geach;

instance Kripke.complete : Complete (Hilbert.KTc) (Kripke.CoreflexiveFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 1, 0, 0⟩});
  . exact eq_Geach;
  . unfold CoreflexiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.coreflexive_def];

end Hilbert.KTc


end LO.Modal

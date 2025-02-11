import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.ReflexiveFrameClass : FrameClass := { F | Reflexive F }

namespace Hilbert.KT

instance Kripke.sound : Sound (Hilbert.KT) (Kripke.ReflexiveFrameClass) := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 0⟩});
  . exact eq_Geach;
  . unfold ReflexiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def];

instance Kripke.consistent : Entailment.Consistent (Hilbert.KT) := by
  convert Hilbert.Geach.Kripke.Consistent (G := {⟨0, 0, 1, 0⟩});
  exact eq_Geach;

instance Kripke.complete : Complete (Hilbert.KT) (Kripke.ReflexiveFrameClass) := by
  convert Hilbert.Geach.Kripke.Complete (G := {⟨0, 0, 1, 0⟩});
  . exact eq_Geach;
  . unfold ReflexiveFrameClass MultiGeacheanConfluentFrameClass MultiGeachean;
    simp [Geachean.reflexive_def];

end Hilbert.KT

end LO.Modal

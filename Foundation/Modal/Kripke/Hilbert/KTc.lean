import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.FrameClass.corefl : FrameClass := { F | Coreflexive F }

namespace Hilbert.KTc

instance Kripke.sound : Sound (Hilbert.KTc) Kripke.FrameClass.corefl := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 1, 0, 0⟩});
  exact eq_Geach;
  . unfold Kripke.FrameClass.corefl FrameClass.multiGeachean MultiGeachean;
    simp [Geachean.reflexive_def, Geachean.coreflexive_def];

instance Kripke.consistent : Entailment.Consistent (Hilbert.KTc) := by
  convert Hilbert.Geach.Kripke.consistent (G := {⟨0, 1, 0, 0⟩});
  exact eq_Geach;

instance Kripke.canonical : Canonical (Hilbert.KTc) Kripke.FrameClass.corefl := ⟨Canonical.coreflexive⟩

instance Kripke.complete : Complete (Hilbert.KTc) Kripke.FrameClass.corefl := inferInstance

end Hilbert.KTc


end LO.Modal

import Foundation.Modal.Kripke.Hilbert.Geach

namespace LO.Modal

open Kripke
open Geachean

protected abbrev Kripke.FrameClass.refl : FrameClass := { F | Reflexive F }

namespace Hilbert.KT

instance Kripke.sound : Sound (Hilbert.KT) Kripke.FrameClass.refl := by
  convert Hilbert.Geach.Kripke.sound (G := {⟨0, 0, 1, 0⟩});
  . exact eq_Geach;
  . unfold Kripke.FrameClass.refl FrameClass.multiGeachean MultiGeachean;
    simp [Geachean.reflexive_def];

instance Kripke.consistent : Entailment.Consistent (Hilbert.KT) := by
  convert Hilbert.Geach.Kripke.consistent (G := {⟨0, 0, 1, 0⟩});
  exact eq_Geach;

instance Kripke.canonical : Canonical (Hilbert.KT) Kripke.FrameClass.refl := ⟨Canonical.reflexive⟩

instance Kripke.complete : Complete (Hilbert.KT) Kripke.FrameClass.refl := inferInstance

end Hilbert.KT

end LO.Modal

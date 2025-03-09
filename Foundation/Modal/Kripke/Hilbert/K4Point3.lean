import Foundation.Modal.Kripke.AxiomWeakPoint3
import Foundation.Modal.Kripke.Hilbert.K4

namespace LO.Modal

open Kripke
open Geachean


abbrev Kripke.FrameClass.trans_weakConnected : FrameClass := { F | Transitive F ∧ WeakConnected F }

namespace Kripke.FrameClass.trans_weakConfluent

protected instance definability_Hilbert
  : FrameClass.DefinedBy Kripke.FrameClass.trans_weakConnected Hilbert.K4Point3.axioms := by
  rw [
    (show Kripke.FrameClass.trans_weakConnected = FrameClass.trans ∩ FrameClass.weakConnected by rfl),
    (show Hilbert.K4Point3.axioms = Hilbert.K4.axioms ∪ {Axioms.WeakPoint3 (.atom 0) (.atom 1)} by aesop)
  ];
  exact FrameClass.definedBy_inter FrameClass.trans (Hilbert.K4.axioms) FrameClass.weakConnected {Axioms.WeakPoint3 (.atom 0) (.atom 1)};

@[simp]
protected lemma nonempty : Kripke.FrameClass.trans_weakConnected.Nonempty := by
  use whitepoint.toFrame;
  simp [Transitive, WeakConnected];

end Kripke.FrameClass.trans_weakConfluent


namespace Hilbert.K4Point3

instance Kripke.sound : Sound (Hilbert.K4Point3) Kripke.FrameClass.trans_weakConnected := inferInstance

instance Kripke.consistent : Entailment.Consistent (Hilbert.K4Point3) := Hilbert.consistent_of_FrameClass Kripke.FrameClass.trans_weakConnected (by simp)

instance Kripke.canonical : Canonical (Hilbert.K4Point3) Kripke.FrameClass.trans_weakConnected := ⟨Canonical.transitive, Canonical.weakConnected⟩

instance Kripke.complete : Complete (Hilbert.K4Point3) Kripke.FrameClass.trans_weakConnected := inferInstance

end Hilbert.K4Point3

end LO.Modal

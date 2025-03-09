import Foundation.Modal.Kripke.AxiomWeakPoint2
import Foundation.Modal.Kripke.Hilbert.K4

namespace LO.Modal

open Kripke
open Geachean


abbrev Kripke.FrameClass.trans_weakConfluent : FrameClass := { F | Transitive F ∧ WeakConfluent F }

namespace Kripke.FrameClass.trans_weakConnected

protected instance definability_Hilbert
  : FrameClass.DefinedBy Kripke.FrameClass.trans_weakConfluent Hilbert.K4Point2.axioms := by
  rw [
    (show Kripke.FrameClass.trans_weakConfluent = FrameClass.trans ∩ FrameClass.weakConfluent by rfl),
    (show Hilbert.K4Point2.axioms = Hilbert.K4.axioms ∪ {Axioms.WeakPoint2 (.atom 0) (.atom 1)} by aesop)
  ];
  exact FrameClass.definedBy_inter FrameClass.trans (Hilbert.K4.axioms) FrameClass.weakConfluent {Axioms.WeakPoint2 (.atom 0) (.atom 1)};

@[simp]
protected lemma nonempty : Kripke.FrameClass.trans_weakConfluent.Nonempty := by
  use whitepoint.toFrame;
  simp [Transitive, WeakConfluent];

end Kripke.FrameClass.trans_weakConnected


namespace Hilbert.K4Point2.Kripke

instance sound : Sound (Hilbert.K4Point2) Kripke.FrameClass.trans_weakConfluent := inferInstance

instance consistent : Entailment.Consistent (Hilbert.K4Point2) := Hilbert.consistent_of_FrameClass Kripke.FrameClass.trans_weakConfluent

instance canonical : Canonical (Hilbert.K4Point2) Kripke.FrameClass.trans_weakConfluent := ⟨Canonical.transitive, Canonical.weakConfluent⟩

instance complete : Complete (Hilbert.K4Point2) Kripke.FrameClass.trans_weakConfluent := inferInstance

end Hilbert.K4Point2.Kripke

end LO.Modal

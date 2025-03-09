import Foundation.Modal.Kripke.Hilbert.S4
import Foundation.Modal.Kripke.AxiomPoint3

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.connected_preorder : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Connected F }

namespace Kripke.ReflexiveTransitiveConnectedFrameClass

instance : FrameClass.DefinedBy Kripke.connected_preorder Hilbert.S4Point3.axioms := by
  rw [
    (show Kripke.connected_preorder = FrameClass.preorder ∩ FrameClass.connected by aesop),
    (show Hilbert.S4Point3.axioms = Hilbert.S4.axioms ∪ {Axioms.Point3 (.atom 0) (.atom 1)} by aesop)
  ];
  exact FrameClass.definedBy_inter FrameClass.preorder (Hilbert.S4.axioms) FrameClass.connected {Axioms.Point3 (.atom 0) (.atom 1)};

@[simp]
protected lemma nonempty : Kripke.connected_preorder.Nonempty := by
  use whitepoint.toFrame;
  simp [Reflexive, Transitive, Connected];

end Kripke.ReflexiveTransitiveConnectedFrameClass


namespace Hilbert.S4Point3.Kripke

instance sound : Sound (Hilbert.S4Point3) Kripke.connected_preorder := inferInstance

instance consistent : Entailment.Consistent (Hilbert.S4Point3) := Hilbert.consistent_of_FrameClass Kripke.connected_preorder

instance canonical : Canonical (Hilbert.S4Point3) Kripke.connected_preorder :=
  ⟨⟨Canonical.reflexive, Canonical.transitive, Canonical.connected⟩⟩

instance complete : Complete (Hilbert.S4Point3) Kripke.connected_preorder := inferInstance

end Hilbert.S4Point3.Kripke


end LO.Modal

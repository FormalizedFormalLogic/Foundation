import Foundation.Modal.Kripke.Hilbert.S4
import Foundation.Modal.Kripke.AxiomDot3

namespace LO.Modal

open Kripke
open Geachean

abbrev Kripke.ReflexiveTransitiveConnectedFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Connected F }

instance Kripke.ReflexiveTransitiveConnectedFrameClass.DefinedByS4Dot3Axioms
  : FrameClass.DefinedBy Kripke.ReflexiveTransitiveConnectedFrameClass Hilbert.S4Dot3.axioms := by
  rw [
    (show ReflexiveTransitiveConnectedFrameClass = ReflexiveTransitiveFrameClass ∩ ConnectedFrameClass by aesop),
    (show Hilbert.S4Dot3.axioms = Hilbert.S4.axioms ∪ {Axioms.Dot3 (.atom 0) (.atom 1)} by aesop)
  ];
  exact FrameClass.definedBy_inter Kripke.ReflexiveTransitiveFrameClass (Hilbert.S4.axioms) ConnectedFrameClass {Axioms.Dot3 (.atom 0) (.atom 1)};

instance : Kripke.ReflexiveTransitiveConnectedFrameClass.IsNonempty := by
  use ⟨Unit, λ _ _ => True⟩;
  simp [Reflexive, Transitive, Connected];


namespace Hilbert.S4Dot3

instance Kripke.sound : Sound (Hilbert.S4Dot3) ReflexiveTransitiveConnectedFrameClass := inferInstance

instance Kripke.consistent : Entailment.Consistent (Hilbert.S4Dot3) :=
  Kripke.Hilbert.consistent_of_FrameClass Kripke.ReflexiveTransitiveConnectedFrameClass

instance Kripke.canonical : Canonical (Hilbert.S4Dot3) ReflexiveTransitiveConnectedFrameClass :=
  ⟨⟨Canonical.reflexive, Canonical.transitive, Canonical.connected⟩⟩

instance Kripke.complete : Complete (Hilbert.S4Dot3) ReflexiveTransitiveConnectedFrameClass := inferInstance

end Hilbert.S4Dot3


end LO.Modal

import Foundation.Modal.Kripke.AxiomWeakDot3
import Foundation.Modal.Kripke.Hilbert.K4

namespace LO.Modal

open Kripke
open Geachean


abbrev Kripke.TransitiveWeakConnectedFrameClass : FrameClass := { F | Transitive F ∧ WeakConnected F }

instance Kripke.TransitiveWeakConnectedFrameClass.DefinedByK4Dot3Axioms
  : FrameClass.DefinedBy Kripke.TransitiveWeakConnectedFrameClass Hilbert.K4Dot3.axioms := by
  rw [
    (show TransitiveWeakConnectedFrameClass = TransitiveFrameClass ∩ WeakConnectedFrameClass by aesop),
    (show Hilbert.K4Dot3.axioms = Hilbert.K4.axioms ∪ {Axioms.WeakDot3 (.atom 0) (.atom 1)} by aesop)
  ];
  exact FrameClass.definedBy_inter Kripke.TransitiveFrameClass (Hilbert.K4.axioms) WeakConnectedFrameClass {Axioms.WeakDot3 (.atom 0) (.atom 1)};

instance : Kripke.TransitiveWeakConnectedFrameClass.IsNonempty := by
  use ⟨Unit, λ _ _ => True⟩;
  simp [Reflexive, Transitive, WeakConnected ];

namespace Hilbert.K4Dot3

instance Kripke.sound : Sound (Hilbert.K4Dot3) (TransitiveWeakConnectedFrameClass) := inferInstance

instance Kripke.consistent : Entailment.Consistent (Hilbert.K4Dot3) := Hilbert.consistent_of_FrameClass TransitiveWeakConnectedFrameClass

instance Kripke.canonical : Canonical (Hilbert.K4Dot3) (TransitiveWeakConnectedFrameClass) := ⟨Canonical.transitive, Canonical.weakConnected⟩

instance Kripke.complete : Complete (Hilbert.K4Dot3) (TransitiveWeakConnectedFrameClass) := inferInstance

end Hilbert.K4Dot3

end LO.Modal

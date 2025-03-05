import Foundation.Modal.Kripke.AxiomWeakPoint3
import Foundation.Modal.Kripke.Hilbert.K4

namespace LO.Modal

open Kripke
open Geachean


abbrev Kripke.TransitiveWeakConnectedFrameClass : FrameClass := { F | Transitive F ∧ WeakConnected F }

instance Kripke.TransitiveWeakConnectedFrameClass.DefinedByK4Point3Axioms
  : FrameClass.DefinedBy Kripke.TransitiveWeakConnectedFrameClass Hilbert.K4Point3.axioms := by
  rw [
    (show TransitiveWeakConnectedFrameClass = TransitiveFrameClass ∩ WeakConnectedFrameClass by aesop),
    (show Hilbert.K4Point3.axioms = Hilbert.K4.axioms ∪ {Axioms.WeakPoint3 (.atom 0) (.atom 1)} by aesop)
  ];
  exact FrameClass.definedBy_inter Kripke.TransitiveFrameClass (Hilbert.K4.axioms) WeakConnectedFrameClass {Axioms.WeakPoint3 (.atom 0) (.atom 1)};

instance : Kripke.TransitiveWeakConnectedFrameClass.IsNonempty := by
  use ⟨Unit, λ _ _ => True⟩;
  simp [Reflexive, Transitive, WeakConnected ];

namespace Hilbert.K4Point3

instance Kripke.sound : Sound (Hilbert.K4Point3) (TransitiveWeakConnectedFrameClass) := inferInstance

instance Kripke.consistent : Entailment.Consistent (Hilbert.K4Point3) := Hilbert.consistent_of_FrameClass TransitiveWeakConnectedFrameClass

instance Kripke.canonical : Canonical (Hilbert.K4Point3) (TransitiveWeakConnectedFrameClass) := ⟨Canonical.transitive, Canonical.weakConnected⟩

instance Kripke.complete : Complete (Hilbert.K4Point3) (TransitiveWeakConnectedFrameClass) := inferInstance

end Hilbert.K4Point3

end LO.Modal

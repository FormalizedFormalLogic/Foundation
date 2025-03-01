import Foundation.Modal.Kripke.AxiomWeakDot2
import Foundation.Modal.Kripke.Hilbert.K4

namespace LO.Modal

open Kripke
open Geachean


abbrev Kripke.TransitiveWeakConfluentFrameClass : FrameClass := { F | Transitive F ∧ WeakConfluent F }

instance Kripke.TransitiveWeakConfluentFrameClass.DefinedByK4Dot2Axioms
  : FrameClass.DefinedBy Kripke.TransitiveWeakConfluentFrameClass Hilbert.K4Dot2.axioms := by
  rw [
    (show TransitiveWeakConfluentFrameClass = TransitiveFrameClass ∩ WeakConfluentFrameClass by aesop),
    (show Hilbert.K4Dot2.axioms = Hilbert.K4.axioms ∪ {Axioms.WeakDot2 (.atom 0) (.atom 1)} by aesop)
  ];
  exact FrameClass.definedBy_inter Kripke.TransitiveFrameClass (Hilbert.K4.axioms) WeakConfluentFrameClass {Axioms.WeakDot2 (.atom 0) (.atom 1)};

instance : Kripke.TransitiveWeakConfluentFrameClass.IsNonempty := by
  use ⟨Unit, λ _ _ => True⟩;
  simp [Reflexive, Transitive, WeakConfluent ];

namespace Hilbert.K4Dot2

instance Kripke.sound : Sound (Hilbert.K4Dot2) (TransitiveWeakConfluentFrameClass) := inferInstance

instance Kripke.consistent : Entailment.Consistent (Hilbert.K4Dot2) := Hilbert.consistent_of_FrameClass TransitiveWeakConfluentFrameClass

instance Kripke.canonical : Canonical (Hilbert.K4Dot2) (TransitiveWeakConfluentFrameClass) := ⟨Canonical.transitive, Canonical.weakConfluent⟩

instance Kripke.complete : Complete (Hilbert.K4Dot2) (TransitiveWeakConfluentFrameClass) := inferInstance

end Hilbert.K4Dot2

end LO.Modal

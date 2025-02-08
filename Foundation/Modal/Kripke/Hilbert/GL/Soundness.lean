import Foundation.Modal.Kripke.AxiomL
import Foundation.Modal.Kripke.Hilbert.Soundness
import Foundation.Modal.Hilbert.WellKnown

namespace LO.Modal

open Formula
open Formula.Kripke
open System
open System.Context
open Kripke

namespace Kripke

instance : TransitiveIrreflexiveFiniteFrameClass.DefinedBy {Axioms.K (atom 0) (atom 1), Axioms.L (atom 0)} :=
  FiniteFrameClass.definedBy_with_axiomK TransitiveIrreflexiveFiniteFrameClass.DefinedByL

instance : TransitiveIrreflexiveFiniteFrameClass.IsNonempty := by
  use ⟨Unit, λ _ _ => False⟩;
  simp [Irreflexive , Transitive];

end Kripke


namespace Hilbert.GL

instance Kripke.finiteSound : Sound (Hilbert.GL) TransitiveIrreflexiveFiniteFrameClass := inferInstance

instance Kripke.consistent : System.Consistent (Hilbert.GL) :=
  Kripke.Hilbert.consistent_of_FiniteFrameClass TransitiveIrreflexiveFiniteFrameClass

end Hilbert.GL

end LO.Modal

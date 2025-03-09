import Foundation.Modal.Kripke.AxiomL
import Foundation.Modal.Kripke.Hilbert.Soundness
import Foundation.Modal.Hilbert.WellKnown

namespace LO.Modal

open Formula
open Formula.Kripke
open Entailment
open Entailment.Context
open Kripke

namespace Kripke

instance : FrameClass.finite_transitive_irreflexive.DefinedBy {Axioms.K (atom 0) (atom 1), Axioms.L (atom 0)} :=
  FiniteFrameClass.definedBy_with_axiomK TransitiveIrreflexiveFiniteFrameClass.DefinedByL

instance : FrameClass.finite_transitive_irreflexive.IsNonempty := by
  use ⟨Unit, λ _ _ => False⟩;
  simp [Irreflexive , Transitive];

end Kripke


namespace Hilbert.GL

instance Kripke.finiteSound : Sound (Hilbert.GL) FrameClass.finite_transitive_irreflexive := inferInstance

instance Kripke.consistent : Entailment.Consistent (Hilbert.GL) :=
  Kripke.Hilbert.consistent_of_FiniteFrameClass FrameClass.finite_transitive_irreflexive

end Hilbert.GL

end LO.Modal

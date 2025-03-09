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

instance : FiniteFrameClass.trans_irrefl.DefinedBy {Axioms.K (atom 0) (atom 1), Axioms.L (atom 0)} :=
  FiniteFrameClass.definedBy_with_axiomK FiniteFrameClass.trans_irrefl.definability

@[simp]
instance : FiniteFrameClass.trans_irrefl.Nonempty := by
  use blackpoint;
  simp [Irreflexive, Transitive];

end Kripke


namespace Hilbert.GL

instance Kripke.finite_sound : Sound (Hilbert.GL) FiniteFrameClass.trans_irrefl := inferInstance

instance Kripke.consistent : Entailment.Consistent (Hilbert.GL) :=
  Kripke.Hilbert.consistent_of_FiniteFrameClass FiniteFrameClass.trans_irrefl

end Hilbert.GL

end LO.Modal

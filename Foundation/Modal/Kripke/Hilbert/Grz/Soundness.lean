import Foundation.Modal.Kripke.AxiomGrz

namespace LO.Modal

open Formula
open Formula.Kripke
open Entailment
open Entailment.Context
open Kripke

namespace Kripke


instance : FiniteFrameClass.strict_preorder.DefinedBy {Axioms.K (atom 0) (atom 1), Axioms.Grz (atom 0)} :=
  FiniteFrameClass.definedBy_with_axiomK FiniteFrameClass.strict_preorder.definability

@[simp]
instance : FiniteFrameClass.strict_preorder.Nonempty := by
  use whitepoint;
  simp [Reflexive, Transitive, AntiSymmetric];


end Kripke

namespace Hilbert.Grz

instance Kripke.finite_sound : Sound (Hilbert.Grz) FiniteFrameClass.strict_preorder := inferInstance

instance Kripke.consistent : Entailment.Consistent (Hilbert.Grz) :=
  Kripke.Hilbert.consistent_of_FiniteFrameClass FiniteFrameClass.strict_preorder

end Hilbert.Grz

end LO.Modal

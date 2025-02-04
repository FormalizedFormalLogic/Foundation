import Foundation.Modal.ComplementClosedConsistentFinset
import Foundation.Modal.Hilbert2.WellKnown
import Foundation.Modal.Kripke2.AxiomGrz
import Foundation.Modal.Kripke2.KT
import Foundation.Modal.Kripke2.Hilbert.Soundness
import Foundation.Modal.System.Grz

namespace LO.Modal

open Formula
open Formula.Kripke
open System
open System.Context
open Kripke

namespace Kripke

instance : ReflexiveTransitiveAntiSymmetricFiniteFrameClass.DefinedBy {Axioms.K (atom 0) (atom 1), Axioms.Grz (atom 0)} :=
  FiniteFrameClass.definedBy_with_axiomK ReflexiveTransitiveAntiSymmetricFiniteFrameClass.definedByAxiomGrz

instance : ReflexiveTransitiveAntiSymmetricFiniteFrameClass.IsNonempty := by
  use ⟨Unit, λ _ _ => True⟩;
  simp [Reflexive, Transitive, AntiSymmetric];

end Kripke

namespace Hilbert.Grz

instance Kripke.consistent : System.Consistent (Hilbert.Grz) :=
  Kripke.Hilbert.consistent_of_FiniteFrameClass ReflexiveTransitiveAntiSymmetricFiniteFrameClass

end Hilbert.Grz

end LO.Modal

import Foundation.Modal.ComplementClosedConsistentFinset
import Foundation.Modal.Hilbert2.WellKnown
import Foundation.Modal.Kripke2.AxiomGrz
import Foundation.Modal.Kripke2.KT
import Foundation.Modal.Kripke2.Soundness
import Foundation.Modal.System.Grz

namespace LO.Modal

namespace Hilbert.Grz

open Formula
open Formula.Kripke
open System
open System.Context
open ComplementClosedConsistentFinset

instance Kripke.consistent : System.Consistent (Hilbert.Grz) := by
  -- haveI := FrameClass.definedBy_with_axiomK TransitiveIrreflexiveFiniteFrameClass.DefinedByL
  sorry;

end Hilbert.Grz

end LO.Modal

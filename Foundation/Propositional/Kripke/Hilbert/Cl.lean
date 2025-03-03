import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.Hilbert.Soundness
import Foundation.Propositional.Kripke.AxiomLEM

namespace LO.Propositional

open Kripke
open Formula.Kripke

open Kripke

namespace Hilbert.Cl.Kripke

instance : EuclideanFrameClass.DefinedBy (Hilbert.Cl.axioms) := FrameClass.definedBy_with_axiomEFQ inferInstance

instance sound : Sound Hilbert.Cl EuclideanFrameClass := inferInstance

instance consistent : Entailment.Consistent Hilbert.Cl := Kripke.Hilbert.consistent_of_FrameClass EuclideanFrameClass

end Hilbert.Cl.Kripke


end LO.Propositional

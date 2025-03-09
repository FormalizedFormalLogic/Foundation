import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.AxiomDummett
import Foundation.Propositional.Kripke.Hilbert.Soundness

namespace LO.Propositional

open Kripke
open Formula.Kripke

namespace Hilbert.LC.Kripke

instance : FrameClass.connected.DefinedBy (Hilbert.LC.axioms) := FrameClass.definedBy_with_axiomEFQ inferInstance

instance sound : Sound Hilbert.LC FrameClass.connected := inferInstance

instance consistent : Entailment.Consistent Hilbert.LC := Kripke.Hilbert.consistent_of_FrameClass FrameClass.connected (by simp)

instance canonical : Canonical Hilbert.LC FrameClass.connected := ⟨Canonical.connected⟩

instance complete : Complete Hilbert.LC FrameClass.connected := inferInstance

end Hilbert.LC.Kripke

end LO.Propositional

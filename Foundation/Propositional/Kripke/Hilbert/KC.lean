import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.AxiomWeakLEM
import Foundation.Propositional.Kripke.Hilbert.Soundness

namespace LO.Propositional

open Kripke
open Formula.Kripke

namespace Hilbert.KC.Kripke

instance : FrameClass.confluent.DefinedBy (Hilbert.KC.axioms) := FrameClass.definedBy_with_axiomEFQ inferInstance

instance sound : Sound Hilbert.KC FrameClass.confluent := inferInstance

instance consistent : Entailment.Consistent Hilbert.KC := Kripke.Hilbert.consistent_of_FrameClass FrameClass.confluent (by simp)

instance canonical : Canonical Hilbert.KC FrameClass.confluent := ⟨Canonical.confluent⟩

instance complete : Complete Hilbert.KC FrameClass.confluent := inferInstance

end Hilbert.KC.Kripke

end LO.Propositional

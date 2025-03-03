import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.Hilbert.Soundness
import Foundation.Propositional.Kripke.Completeness
import Foundation.Propositional.Kripke.AxiomWeakLEM

namespace LO.Propositional

open Kripke
open Formula.Kripke

namespace Hilbert.KC.Kripke

instance : ConfluentFrameClass.DefinedBy (Hilbert.KC.axioms) := FrameClass.definedBy_with_axiomEFQ inferInstance

instance sound : Sound Hilbert.KC ConfluentFrameClass := inferInstance

instance consistent : Entailment.Consistent Hilbert.KC := Kripke.Hilbert.consistent_of_FrameClass ConfluentFrameClass

instance canonical : Canonical Hilbert.KC ConfluentFrameClass := ⟨Canonical.confluent⟩

instance complete : Complete Hilbert.KC ConfluentFrameClass := inferInstance

end Hilbert.KC.Kripke


end LO.Propositional

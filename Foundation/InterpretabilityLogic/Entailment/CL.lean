import Foundation.Modal.Entailment.GL
import Foundation.InterpretabilityLogic.Entailment.Basic

namespace LO.InterpretabilityLogic.Entailment

variable {S F : Type*} [InterpretabilityLogicalConnective F] [Entailment S F]

/-- Entailment for conservatibity logic -/
protected class CL (𝓢 : S) extends Modal.Entailment.GL 𝓢, HasAxiomJ1 𝓢, HasAxiomJ2 𝓢, HasAxiomJ3 𝓢, HasAxiomJ4 𝓢

end LO.InterpretabilityLogic.Entailment

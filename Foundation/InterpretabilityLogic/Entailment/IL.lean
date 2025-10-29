import Foundation.InterpretabilityLogic.Entailment.CL

namespace LO.InterpretabilityLogic.Entailment

variable {S F : Type*} [InterpretabilityLogicalConnective F] [Entailment S F]

/-- Entailment for interpretability logic -/
protected class IL (𝓢 : S) extends InterpretabilityLogic.Entailment.CL 𝓢, HasAxiomJ5 𝓢

end LO.InterpretabilityLogic.Entailment

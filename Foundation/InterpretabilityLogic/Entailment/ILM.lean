import Foundation.InterpretabilityLogic.Entailment.IL

namespace LO.InterpretabilityLogic.Entailment

variable {S F : Type*} [InterpretabilityLogicalConnective F] [Entailment S F]

/-- Entailment for interpretability logic with Montagna's principle -/
protected class ILM (𝓢 : S) extends InterpretabilityLogic.Entailment.IL 𝓢, HasAxiomMP 𝓢

end LO.InterpretabilityLogic.Entailment

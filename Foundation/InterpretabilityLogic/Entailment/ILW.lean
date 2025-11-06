import Foundation.InterpretabilityLogic.Entailment.IL

namespace LO.InterpretabilityLogic.Entailment

variable {S F : Type*} [InterpretabilityLogicalConnective F] [Entailment S F]

/-- Entailment for interpretability logic with persistence principle -/
protected class ILW (𝓢 : S) extends InterpretabilityLogic.Entailment.IL 𝓢, HasAxiomW 𝓢

end LO.InterpretabilityLogic.Entailment

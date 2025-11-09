import Foundation.InterpretabilityLogic.Entailment.IL

namespace LO.InterpretabilityLogic.Entailment

variable {S F : Type*} [InterpretabilityLogicalConnective F] [Entailment S F]

protected class ILW (𝓢 : S) extends InterpretabilityLogic.Entailment.IL 𝓢, HasAxiomW 𝓢

end LO.InterpretabilityLogic.Entailment

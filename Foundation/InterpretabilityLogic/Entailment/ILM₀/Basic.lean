import Foundation.InterpretabilityLogic.Entailment.IL
import Foundation.InterpretabilityLogic.Entailment.ILMinus_M
import Foundation.InterpretabilityLogic.Entailment.ILW

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ : F}

protected class ILM₀ (𝓢 : S) extends InterpretabilityLogic.Entailment.IL 𝓢, HasAxiomM₀ 𝓢

variable [Entailment.ILM₀ 𝓢]

end LO.InterpretabilityLogic.Entailment

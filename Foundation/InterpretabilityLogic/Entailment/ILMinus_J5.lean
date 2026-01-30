module

public import Foundation.InterpretabilityLogic.Entailment.ILMinus

@[expose] public section

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S}

protected class ILMinus_J5 (𝓢 : S) extends Entailment.ILMinus 𝓢, HasAxiomJ5 𝓢

end LO.InterpretabilityLogic.Entailment
end

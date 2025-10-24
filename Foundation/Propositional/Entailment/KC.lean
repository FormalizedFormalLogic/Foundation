import Foundation.Propositional.Entailment.Basic

namespace LO.Entailment

open FiniteContext

variable {S F : Type*} [LogicalConnective F] [DecidableEq F] [Entailment S F]
variable {𝓢 : S} [Entailment.KC 𝓢]

end LO.Entailment

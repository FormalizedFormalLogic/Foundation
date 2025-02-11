import Foundation.Modal.Entailment.S4

namespace LO.Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.S4Dot2 𝓢]

end LO.Entailment

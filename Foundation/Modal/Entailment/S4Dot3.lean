import Foundation.Modal.Entailment.S4

namespace LO.Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.Modal.S4Point3 𝓢]

end LO.Entailment

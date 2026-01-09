module
import Foundation.Modal.Entailment.S4

namespace LO.Modal.Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment S F]
variable {𝓢 : S} [Entailment.S4Point2 𝓢]

end LO.Modal.Entailment

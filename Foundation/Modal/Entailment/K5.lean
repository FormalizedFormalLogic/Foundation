import Foundation.Modal.Entailment.K

namespace LO.Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.Modal.K5 𝓢]

end LO.Entailment

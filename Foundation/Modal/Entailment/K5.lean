import Foundation.Modal.Entailment.K

namespace LO.Modal.Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.K5 𝓢]

end LO.Modal.Entailment

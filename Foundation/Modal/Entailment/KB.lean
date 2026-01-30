module

public import Foundation.Modal.Entailment.K

@[expose] public section

namespace LO.Modal.Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment S F]
variable {𝓢 : S} [Entailment.KB 𝓢]

end LO.Modal.Entailment
end

import Foundation.Modal.Entailment.K
import Foundation.Modal.Entailment.END

namespace LO.Modal.Entailment

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S}

noncomputable instance [Entailment.KD 𝓢] : Entailment.END 𝓢 where

end LO.Modal.Entailment

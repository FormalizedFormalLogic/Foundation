import Foundation.Modal.Entailment.EMC
import Foundation.Modal.Entailment.EN
import Foundation.Modal.Entailment.K

namespace LO.Modal.Entailment

open LO.Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S}

instance [Entailment.EMCN 𝓢] : Entailment.K 𝓢 where
instance [Entailment.K 𝓢] : Entailment.EMCN 𝓢 where
  re h := by
    apply K_intro
    . exact axiomK' $ nec $ K_left h
    . exact axiomK' $ nec $ K_right h

end LO.Modal.Entailment

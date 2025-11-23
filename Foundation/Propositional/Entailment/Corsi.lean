import Foundation.Propositional.Entailment.Corsi.Basic
import Foundation.Propositional.Entailment.Corsi.F
import Foundation.Propositional.Entailment.Corsi.VF

namespace LO.Propositional.Entailment

variable {S F : Type*} [DecidableEq F] [LogicalConnective F] [Entailment S F] {𝓢 : S}

instance [Entailment.F 𝓢] : Entailment.VF 𝓢 where

end LO.Propositional.Entailment

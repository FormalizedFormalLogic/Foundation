import Foundation.InterpretabilityLogic.Entailment.IL
import Foundation.InterpretabilityLogic.Entailment.IL_KW1Zero
import Foundation.InterpretabilityLogic.Entailment.IL_KW2
import Foundation.InterpretabilityLogic.Entailment.ILM
import Foundation.InterpretabilityLogic.Entailment.ILM₀.Basic
import Foundation.InterpretabilityLogic.Entailment.ILMinus
import Foundation.InterpretabilityLogic.Entailment.ILMinus_J1
import Foundation.InterpretabilityLogic.Entailment.ILMinus_J2
import Foundation.InterpretabilityLogic.Entailment.ILMinus_J4
import Foundation.InterpretabilityLogic.Entailment.ILMinus_J5
import Foundation.InterpretabilityLogic.Entailment.ILMinus_M
import Foundation.InterpretabilityLogic.Entailment.ILP
import Foundation.InterpretabilityLogic.Entailment.ILR
import Foundation.InterpretabilityLogic.Entailment.ILRStar
import Foundation.InterpretabilityLogic.Entailment.ILRW
import Foundation.InterpretabilityLogic.Entailment.ILW
import Foundation.InterpretabilityLogic.Entailment.ILWM₀
import Foundation.InterpretabilityLogic.Entailment.ILWStar.Basic
import Foundation.InterpretabilityLogic.Entailment.ILWStar.M₀

namespace LO.InterpretabilityLogic.Entailment

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S}

instance [Entailment.ILWM₀ 𝓢] : Entailment.ILWStar 𝓢 where

instance [Entailment.ILM 𝓢] : Entailment.ILRW 𝓢 where
instance [Entailment.ILW 𝓢] : Entailment.IL_KW2 𝓢 where
instance [Entailment.ILW 𝓢] : Entailment.HasAxiomF 𝓢 := «IL(KW2)_⊢_F»

instance [Entailment.ILM 𝓢] : Entailment.ILRStar 𝓢 where
instance [Entailment.ILM 𝓢] : Entailment.ILW 𝓢 where
instance [Entailment.ILM 𝓢] : Entailment.ILR 𝓢 where
instance [Entailment.ILM 𝓢] : Entailment.ILRW 𝓢 where

instance [Entailment.ILP 𝓢] : Entailment.ILW 𝓢 where
instance [Entailment.ILP 𝓢] : Entailment.ILR 𝓢 where
instance [Entailment.ILP 𝓢] : Entailment.ILRW 𝓢 where
instance [Entailment.ILP 𝓢] : Entailment.ILRStar 𝓢 where

end LO.InterpretabilityLogic.Entailment

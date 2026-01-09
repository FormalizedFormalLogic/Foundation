module
import Foundation.InterpretabilityLogic.Entailment.IL
import Foundation.InterpretabilityLogic.Entailment.IL_KW1Zero
import Foundation.InterpretabilityLogic.Entailment.IL_KW2
import Foundation.InterpretabilityLogic.Entailment.IL_M
import Foundation.InterpretabilityLogic.Entailment.IL_M₀_W
import Foundation.InterpretabilityLogic.Entailment.IL_M₀
import Foundation.InterpretabilityLogic.Entailment.IL_P
import Foundation.InterpretabilityLogic.Entailment.IL_R
import Foundation.InterpretabilityLogic.Entailment.IL_R_W
import Foundation.InterpretabilityLogic.Entailment.IL_Rstar
import Foundation.InterpretabilityLogic.Entailment.IL_W
import Foundation.InterpretabilityLogic.Entailment.IL_Wstar
import Foundation.InterpretabilityLogic.Entailment.ILMinus
import Foundation.InterpretabilityLogic.Entailment.ILMinus_J1
import Foundation.InterpretabilityLogic.Entailment.ILMinus_J2
import Foundation.InterpretabilityLogic.Entailment.ILMinus_J4
import Foundation.InterpretabilityLogic.Entailment.ILMinus_J5
import Foundation.InterpretabilityLogic.Entailment.ILMinus_M

namespace LO.InterpretabilityLogic.Entailment

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S}

instance [Entailment.IL_M₀_W 𝓢] : Entailment.IL_Wstar 𝓢 where

instance [Entailment.IL_M 𝓢] : Entailment.IL_R_W 𝓢 where
instance [Entailment.IL_W 𝓢] : Entailment.IL_KW2 𝓢 where
instance [Entailment.IL_W 𝓢] : Entailment.HasAxiomF 𝓢 := «IL(KW2)_⊢_F»

instance [Entailment.IL_M 𝓢] : Entailment.IL_Rstar 𝓢 where
instance [Entailment.IL_M 𝓢] : Entailment.IL_W 𝓢 where
instance [Entailment.IL_M 𝓢] : Entailment.IL_R 𝓢 where
instance [Entailment.IL_M 𝓢] : Entailment.IL_R_W 𝓢 where

instance [Entailment.IL_P 𝓢] : Entailment.IL_W 𝓢 where
instance [Entailment.IL_P 𝓢] : Entailment.IL_R 𝓢 where
instance [Entailment.IL_P 𝓢] : Entailment.IL_R_W 𝓢 where
instance [Entailment.IL_P 𝓢] : Entailment.IL_Rstar 𝓢 where

instance [Entailment.IL_Wstar 𝓢] : Entailment.IL_W 𝓢 where
instance [Entailment.IL_Wstar 𝓢] : Entailment.IL_M₀ 𝓢 where

end LO.InterpretabilityLogic.Entailment

module

public import Foundation.InterpretabilityLogic.Entailment.IL
public import Foundation.InterpretabilityLogic.Entailment.IL_KW1Zero
public import Foundation.InterpretabilityLogic.Entailment.IL_KW2
public import Foundation.InterpretabilityLogic.Entailment.IL_M
public import Foundation.InterpretabilityLogic.Entailment.IL_M₀_W
public import Foundation.InterpretabilityLogic.Entailment.IL_M₀
public import Foundation.InterpretabilityLogic.Entailment.IL_P
public import Foundation.InterpretabilityLogic.Entailment.IL_R
public import Foundation.InterpretabilityLogic.Entailment.IL_R_W
public import Foundation.InterpretabilityLogic.Entailment.IL_Rstar
public import Foundation.InterpretabilityLogic.Entailment.IL_W
public import Foundation.InterpretabilityLogic.Entailment.IL_Wstar
public import Foundation.InterpretabilityLogic.Entailment.ILMinus
public import Foundation.InterpretabilityLogic.Entailment.ILMinus_J1
public import Foundation.InterpretabilityLogic.Entailment.ILMinus_J2
public import Foundation.InterpretabilityLogic.Entailment.ILMinus_J4
public import Foundation.InterpretabilityLogic.Entailment.ILMinus_J5
public import Foundation.InterpretabilityLogic.Entailment.ILMinus_M

@[expose] public section

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
end

import Foundation.InterpretabilityLogic.Entailment.IL
import Foundation.InterpretabilityLogic.Entailment.ILMinus_M

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ : F}

/-- Entailment for interpretability logic with Montagna's principle -/
protected class ILM (𝓢 : S) extends InterpretabilityLogic.Entailment.IL 𝓢, HasAxiomM 𝓢

variable [Entailment.ILM 𝓢]
instance : Entailment.ILMinus_M 𝓢 where

end LO.InterpretabilityLogic.Entailment

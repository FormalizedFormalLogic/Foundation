import Foundation.InterpretabilityLogic.Entailment.ILMinus

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S}

protected class ILMinus_J1 (𝓢 : S) extends Entailment.ILMinus 𝓢, HasAxiomJ1 𝓢

variable [Entailment.ILMinus_J1 𝓢]

instance : HasAxiomJ1' 𝓢 := ⟨by
  intro φ;
  exact axiomJ1! ⨀ (nec $ C_id (φ := φ));
⟩


protected class ILMinus_J1' (𝓢 : S) extends Entailment.ILMinus 𝓢, HasAxiomJ1' 𝓢

variable [Entailment.ILMinus_J1' 𝓢]

instance : HasAxiomJ1 𝓢 := ⟨by
  intro φ ψ;
  have := CCRhdRhdLC! (𝓢 := 𝓢) (φ := φ) (ψ := ψ) (χ := ψ);
  apply C_trans this;
  apply CCC (𝓢 := 𝓢) ⨀ axiomJ1'!;
⟩

end LO.InterpretabilityLogic.Entailment

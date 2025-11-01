import Foundation.Modal.Entailment.GL
import Foundation.InterpretabilityLogic.Entailment.ILMinus

namespace LO.InterpretabilityLogic.Entailment

variable {S F : Type*} [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S}

/-- Entailment for conservatibity logic -/
protected class CL (𝓢 : S) extends Modal.Entailment.GL 𝓢, HasAxiomJ1 𝓢, HasAxiomJ2 𝓢, HasAxiomJ3 𝓢, HasAxiomJ4 𝓢

variable [Entailment.CL 𝓢]

instance : HasAxiomJ6 𝓢 := ⟨by sorry⟩

instance : HasRule1 𝓢 := ⟨by sorry⟩

instance : HasRule2 𝓢 := ⟨by sorry⟩

instance : Entailment.ILMinus 𝓢 where

end LO.InterpretabilityLogic.Entailment

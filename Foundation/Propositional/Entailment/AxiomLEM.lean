module
public import Foundation.Propositional.Entailment.Minimal.Basic

@[expose] public section

namespace LO.Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

protected abbrev LEM := φ ⋎ ∼φ

end LO.Axioms


namespace LO.Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

class HasAxiomLEM (𝓢 : S)  where
  lem {φ : F} : 𝓢 ⊢! Axioms.LEM φ
export HasAxiomLEM (lem)

@[simp] lemma lem! [HasAxiomLEM 𝓢] : 𝓢 ⊢ φ ⋎ ∼φ := ⟨lem⟩


section

variable [LogicalConnective F] [Entailment S F] [Entailment.Minimal 𝓢]

namespace FiniteContext

instance [Entailment.HasAxiomLEM 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomLEM Γ := ⟨of lem⟩

end FiniteContext


namespace Context

instance [Entailment.HasAxiomLEM 𝓢] (Γ : Context F 𝓢) : HasAxiomLEM Γ := ⟨of lem⟩

end Context

end

end LO.Entailment

end

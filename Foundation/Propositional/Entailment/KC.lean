module
public import Foundation.Propositional.Entailment.Int.Basic

@[expose] public section

namespace LO.Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

protected abbrev WLEM := ∼φ ⋎ ∼∼φ

end LO.Axioms


namespace LO.Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

class HasAxiomWLEM (𝓢 : S)  where
  wlem {φ : F} : 𝓢 ⊢! Axioms.WLEM φ
export HasAxiomWLEM (wlem)

@[simp] lemma wlem! [HasAxiomWLEM 𝓢] : 𝓢 ⊢ Axioms.WLEM φ := ⟨wlem⟩


section

variable [LogicalConnective F] [Entailment S F] [Entailment.Minimal 𝓢]

namespace FiniteContext

instance [Entailment.HasAxiomWLEM 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomWLEM Γ := ⟨of wlem⟩

end FiniteContext


namespace Context

instance [Entailment.HasAxiomWLEM 𝓢] (Γ : Context F 𝓢) : HasAxiomWLEM Γ := ⟨of wlem⟩

end Context

end


protected class KC (𝓢 : S) extends Entailment.Int 𝓢, HasAxiomWLEM 𝓢


end LO.Entailment

end

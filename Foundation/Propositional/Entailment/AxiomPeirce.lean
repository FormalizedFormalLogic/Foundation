module
public import Foundation.Propositional.Entailment.Minimal.Basic

@[expose] public section

namespace LO.Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

protected abbrev Peirce := ((φ 🡒 ψ) 🡒 φ) 🡒 φ

end LO.Axioms


namespace LO.Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

class HasAxiomPeirce (𝓢 : S)  where
  peirce {φ ψ : F} : 𝓢 ⊢! Axioms.Peirce φ ψ
export HasAxiomPeirce (peirce)

@[simp] lemma peirce! [HasAxiomPeirce 𝓢] : 𝓢 ⊢ ((φ 🡒 ψ) 🡒 φ) 🡒 φ := ⟨peirce⟩


section

variable [LogicalConnective F] [Entailment S F] [Entailment.Minimal 𝓢]

namespace FiniteContext

instance [Entailment.HasAxiomPeirce 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomPeirce Γ := ⟨of peirce⟩

end FiniteContext


namespace Context

instance [Entailment.HasAxiomPeirce 𝓢] (Γ : Context F 𝓢) : HasAxiomPeirce Γ := ⟨of peirce⟩

end Context

end

end LO.Entailment

end

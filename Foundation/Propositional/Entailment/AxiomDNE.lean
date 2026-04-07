module

public import Foundation.Propositional.Entailment.Minimal.Basic

@[expose] public section

namespace LO.Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

protected abbrev DNE := ∼∼φ 🡒 φ

end LO.Axioms


namespace LO.Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

class HasAxiomDNE (𝓢 : S)  where
  dne {φ : F} : 𝓢 ⊢! Axioms.DNE φ
export HasAxiomDNE (dne)

@[simp] lemma dne! [HasAxiomDNE 𝓢] : 𝓢 ⊢ ∼∼φ 🡒 φ  := ⟨dne⟩

def of_NN [ModusPonens 𝓢] [HasAxiomDNE 𝓢] (b : 𝓢 ⊢! ∼∼φ) : 𝓢 ⊢! φ := dne ⨀ b
@[grind ⇒] lemma of_NN! [ModusPonens 𝓢] [HasAxiomDNE 𝓢] (h : 𝓢 ⊢ ∼∼φ) : 𝓢 ⊢ φ := ⟨of_NN h.some⟩

section

variable [LogicalConnective F] [Entailment S F] [Entailment.Minimal 𝓢]

namespace FiniteContext

instance [Entailment.HasAxiomDNE 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomDNE Γ := ⟨of dne⟩

end FiniteContext


namespace Context

instance [Entailment.HasAxiomDNE 𝓢] (Γ : Context F 𝓢) : HasAxiomDNE Γ := ⟨of dne⟩

end Context

end


end LO.Entailment

end

module
public import Foundation.Propositional.Entailment.Int.Basic

@[expose] public section

namespace LO.Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

protected abbrev KreiselPutnam :=  (∼φ 🡒 ψ ⋎ χ) 🡒 (∼φ 🡒 ψ) ⋎ (∼φ 🡒 χ)

end LO.Axioms


namespace LO.Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

class HasAxiomKreiselPutnam (𝓢 : S)  where
  kreiselputnam {φ ψ χ : F} : 𝓢 ⊢! Axioms.KreiselPutnam φ ψ χ
export HasAxiomKreiselPutnam (kreiselputnam)

@[simp] lemma kreiselputnam! [HasAxiomKreiselPutnam 𝓢] : 𝓢 ⊢ Axioms.KreiselPutnam φ ψ χ := ⟨kreiselputnam⟩

section

variable [ModusPonens 𝓢] [HasAxiomKreiselPutnam 𝓢]

def kreiselputnam' (h : 𝓢 ⊢! (∼φ 🡒 ψ ⋎ χ)) : 𝓢 ⊢! (∼φ 🡒 ψ) ⋎ (∼φ 🡒 χ) := kreiselputnam ⨀ h
lemma kreiselputnam'! (h : 𝓢 ⊢ (∼φ 🡒 ψ ⋎ χ)) : 𝓢 ⊢ (∼φ 🡒 ψ) ⋎ (∼φ 🡒 χ) := ⟨kreiselputnam' h.some⟩

end


section

variable [LogicalConnective F] [Entailment S F] [Entailment.Minimal 𝓢]

namespace FiniteContext

instance [Entailment.HasAxiomKreiselPutnam 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomKreiselPutnam Γ := ⟨of kreiselputnam⟩

end FiniteContext


namespace Context

instance [Entailment.HasAxiomKreiselPutnam 𝓢] (Γ : Context F 𝓢) : HasAxiomKreiselPutnam Γ := ⟨of kreiselputnam⟩

end Context

end


protected class KreiselPutnam (𝓢 : S) extends Entailment.Int 𝓢, HasAxiomKreiselPutnam 𝓢


end LO.Entailment

end

import Foundation.Propositional.Entailment.Int.Basic


namespace LO.Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

protected abbrev KrieselPutnam :=  (∼φ ➝ ψ ⋎ χ) ➝ (∼φ ➝ ψ) ⋎ (∼φ ➝ χ)

end LO.Axioms


namespace LO.Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

class HasAxiomKrieselPutnam (𝓢 : S)  where
  krieselputnam {φ ψ χ : F} : 𝓢 ⊢! Axioms.KrieselPutnam φ ψ χ
export HasAxiomKrieselPutnam (krieselputnam)

@[simp] lemma krieselputnam! [HasAxiomKrieselPutnam 𝓢] : 𝓢 ⊢ Axioms.KrieselPutnam φ ψ χ := ⟨krieselputnam⟩

section

variable [ModusPonens 𝓢] [HasAxiomKrieselPutnam 𝓢]

def krieselputnam' (h : 𝓢 ⊢! (∼φ ➝ ψ ⋎ χ)) : 𝓢 ⊢! (∼φ ➝ ψ) ⋎ (∼φ ➝ χ) := krieselputnam ⨀ h
lemma krieselputnam'! (h : 𝓢 ⊢ (∼φ ➝ ψ ⋎ χ)) : 𝓢 ⊢ (∼φ ➝ ψ) ⋎ (∼φ ➝ χ) := ⟨krieselputnam' h.some⟩

end


section

variable [LogicalConnective F] [Entailment S F] [Entailment.Minimal 𝓢]

namespace FiniteContext

instance [Entailment.HasAxiomKrieselPutnam 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomKrieselPutnam Γ := ⟨of krieselputnam⟩

end FiniteContext


namespace Context

instance [Entailment.HasAxiomKrieselPutnam 𝓢] (Γ : Context F 𝓢) : HasAxiomKrieselPutnam Γ := ⟨of krieselputnam⟩

end Context

end


protected class KrieselPutnam (𝓢 : S) extends Entailment.Int 𝓢, HasAxiomKrieselPutnam 𝓢


end LO.Entailment

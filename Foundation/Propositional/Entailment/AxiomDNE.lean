import Foundation.Logic.Entailment


namespace LO.Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

protected abbrev DNE := ∼∼φ ➝ φ

end LO.Axioms


namespace LO.Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment F S]
variable {𝓢 : S} {φ ψ χ : F}

class HasAxiomDNE (𝓢 : S)  where
  DNE {φ : F} : 𝓢 ⊢! Axioms.DNE φ
export HasAxiomDNE (DNE)

@[simp] lemma dne! [HasAxiomDNE 𝓢] : 𝓢 ⊢ ∼∼φ ➝ φ  := ⟨DNE⟩

end LO.Entailment

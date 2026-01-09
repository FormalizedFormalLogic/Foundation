module
import Foundation.Logic.Entailment


namespace LO.Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

protected abbrev ElimContra := (∼ψ ➝ ∼φ) ➝ (φ ➝ ψ)

end LO.Axioms


namespace LO.Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

class HasAxiomElimContra (𝓢 : S)  where
  elimContra {φ ψ : F} : 𝓢 ⊢! Axioms.ElimContra φ ψ
export HasAxiomElimContra (elimContra)

@[simp] lemma elim_contra! [HasAxiomElimContra 𝓢] : 𝓢 ⊢ (∼ψ ➝ ∼φ) ➝ (φ ➝ ψ)  := ⟨elimContra⟩

end LO.Entailment

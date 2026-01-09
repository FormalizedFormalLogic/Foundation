module
import Foundation.Propositional.Entailment.Int.Basic


namespace LO.Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

protected abbrev Scott := ((∼∼φ ➝ φ) ➝ (φ ⋎ ∼φ)) ➝ ∼φ ⋎ ∼∼φ

end LO.Axioms


namespace LO.Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

class HasAxiomScott (𝓢 : S)  where
  scott {φ : F} : 𝓢 ⊢! Axioms.Scott φ
export HasAxiomScott (scott)

@[simp] lemma scott! [HasAxiomScott 𝓢] : 𝓢 ⊢ Axioms.Scott φ := ⟨scott⟩


section

variable [LogicalConnective F] [Entailment S F] [Entailment.Minimal 𝓢]

namespace FiniteContext

instance [Entailment.HasAxiomScott 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomScott Γ := ⟨of scott⟩

end FiniteContext


namespace Context

instance [Entailment.HasAxiomScott 𝓢] (Γ : Context F 𝓢) : HasAxiomScott Γ := ⟨of scott⟩

end Context

end


protected class Scott (𝓢 : S) extends Entailment.Int 𝓢, HasAxiomScott 𝓢


end LO.Entailment

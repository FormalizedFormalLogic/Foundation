module
import Foundation.Logic.Entailment
import Foundation.Propositional.Entailment.Minimal.Basic


namespace LO.Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

protected abbrev EFQ := ⊥ ➝ φ

end LO.Axioms



namespace LO.Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

class HasAxiomEFQ (𝓢 : S)  where
  efq {φ : F} : 𝓢 ⊢! Axioms.EFQ φ
export HasAxiomEFQ (efq)

@[simp] lemma efq! [Entailment.HasAxiomEFQ 𝓢] : 𝓢 ⊢ ⊥ ➝ φ := ⟨efq⟩

def of_O [ModusPonens 𝓢] [Entailment.HasAxiomEFQ 𝓢] (b : 𝓢 ⊢! ⊥) : 𝓢 ⊢! φ := efq ⨀ b
@[grind ⇒] lemma of_O! [ModusPonens 𝓢]  [Entailment.HasAxiomEFQ 𝓢] (h : 𝓢 ⊢ ⊥) : 𝓢 ⊢ φ := ⟨of_O h.some⟩


instance [(𝓢 : S) → ModusPonens 𝓢] [(𝓢 : S) → HasAxiomEFQ 𝓢] : DeductiveExplosion S := ⟨fun b _ ↦ efq ⨀ b⟩


section

variable [LogicalConnective F] [Entailment S F] [Entailment.Minimal 𝓢]

namespace FiniteContext

instance [Entailment.HasAxiomEFQ 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomEFQ Γ := ⟨of efq⟩

instance [Entailment.HasAxiomEFQ 𝓢] : DeductiveExplosion (FiniteContext F 𝓢) := inferInstance

end FiniteContext


namespace Context

instance [Entailment.HasAxiomEFQ 𝓢] (Γ : Context F 𝓢) : HasAxiomEFQ Γ := ⟨of efq⟩

instance [Entailment.HasAxiomEFQ 𝓢] : DeductiveExplosion (FiniteContext F 𝓢) := inferInstance

end Context

end


end LO.Entailment

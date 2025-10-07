import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.Propositional.Axioms

namespace LO.Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment F S]
variable {𝓢 : S} {φ ψ χ : F}


class HasAxiomWeakLEM (𝓢 : S) where
  wlem (φ : F) : 𝓢 ⊢! Axioms.WeakLEM φ

section

variable [HasAxiomWeakLEM 𝓢]

def wlem [HasAxiomWeakLEM 𝓢] : 𝓢 ⊢! ∼φ ⋎ ∼∼φ := HasAxiomWeakLEM.wlem φ
@[simp] lemma wlem! : 𝓢 ⊢ ∼φ ⋎ ∼∼φ := ⟨wlem⟩

end


class HasAxiomDummett (𝓢 : S) where
  dummett (φ ψ : F) : 𝓢 ⊢! Axioms.Dummett φ ψ

section

variable [HasAxiomDummett 𝓢]

def dummett : 𝓢 ⊢! (φ ➝ ψ) ⋎ (ψ ➝ φ) := HasAxiomDummett.dummett φ ψ
@[simp] lemma dummett! : 𝓢 ⊢ Axioms.Dummett φ ψ := ⟨dummett⟩

end


class HasAxiomKrieselPutnam (𝓢 : S) where
  krieselputnam (φ ψ χ : F) : 𝓢 ⊢! Axioms.KrieselPutnam φ ψ χ

section

variable [HasAxiomKrieselPutnam 𝓢]

def krieselputnam : 𝓢 ⊢! (∼φ ➝ ψ ⋎ χ) ➝ (∼φ ➝ ψ) ⋎ (∼φ ➝ χ) := HasAxiomKrieselPutnam.krieselputnam φ ψ χ
@[simp] lemma krieselputnam! : 𝓢 ⊢ (∼φ ➝ ψ ⋎ χ) ➝ (∼φ ➝ ψ) ⋎ (∼φ ➝ χ) := ⟨krieselputnam⟩

variable [Entailment.Minimal 𝓢]

instance (Γ : FiniteContext F 𝓢) : HasAxiomKrieselPutnam Γ := ⟨fun _ _ _ ↦ FiniteContext.of krieselputnam⟩
instance (Γ : Context F 𝓢) : HasAxiomKrieselPutnam Γ := ⟨fun _ _ _ ↦ Context.of krieselputnam⟩

def krieselputnam' (h : 𝓢 ⊢! (∼φ ➝ ψ ⋎ χ)) : 𝓢 ⊢! (∼φ ➝ ψ) ⋎ (∼φ ➝ χ) := krieselputnam ⨀ h
lemma krieselputnam'! (h : 𝓢 ⊢ (∼φ ➝ ψ ⋎ χ)) : 𝓢 ⊢ (∼φ ➝ ψ) ⋎ (∼φ ➝ χ) := ⟨krieselputnam' h.some⟩

end


class HasAxiomScott (𝓢 : S) where
  scott (φ : F) : 𝓢 ⊢! Axioms.Scott φ

section

variable [HasAxiomScott 𝓢]

def scott : 𝓢 ⊢! ((∼∼φ ➝ φ) ➝ (φ ⋎ ∼φ)) ➝ ∼φ ⋎ ∼∼φ := HasAxiomScott.scott φ
@[simp] lemma scott! : 𝓢 ⊢ ((∼∼φ ➝ φ) ➝ (φ ⋎ ∼φ)) ➝ ∼φ ⋎ ∼∼φ := ⟨scott⟩

end


class HasAxiomPeirce (𝓢 : S) where
  peirce (φ ψ : F) : 𝓢 ⊢! Axioms.Peirce φ ψ

section

variable [HasAxiomPeirce 𝓢]

def peirce : 𝓢 ⊢! ((φ ➝ ψ) ➝ φ) ➝ φ := HasAxiomPeirce.peirce φ ψ
@[simp] lemma peirce! : 𝓢 ⊢ ((φ ➝ ψ) ➝ φ) ➝ φ := ⟨peirce⟩

end


section

variable (𝓢 : S)

protected class KC extends Entailment.Int 𝓢, HasAxiomWeakLEM 𝓢

protected class LC extends Entailment.Int 𝓢, HasAxiomDummett 𝓢

protected class KrieselPutnam extends Entailment.Int 𝓢, HasAxiomKrieselPutnam 𝓢

protected class Sc extends Entailment.Int 𝓢, HasAxiomScott 𝓢

end


end LO.Entailment

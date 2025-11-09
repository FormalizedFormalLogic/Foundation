import Foundation.Propositional.Entailment.KC


namespace LO.Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

protected abbrev Dummett := (φ ➝ ψ) ⋎ (ψ ➝ φ)

end LO.Axioms


namespace LO.Entailment

variable {S F : Type*} [LogicalConnective F] [Entailment S F]
variable {𝓢 : S} {φ ψ χ : F}

class HasAxiomDummett (𝓢 : S)  where
  dummett {φ ψ : F} : 𝓢 ⊢! Axioms.Dummett φ ψ
export HasAxiomDummett (dummett)

@[simp] lemma dummett! [HasAxiomDummett 𝓢] : 𝓢 ⊢ Axioms.Dummett φ ψ := ⟨dummett⟩


section

variable [LogicalConnective F] [Entailment S F] [Entailment.Minimal 𝓢]

namespace FiniteContext

instance [Entailment.HasAxiomDummett 𝓢] (Γ : FiniteContext F 𝓢) : HasAxiomDummett Γ := ⟨of dummett⟩

end FiniteContext


namespace Context

instance [Entailment.HasAxiomDummett 𝓢] (Γ : Context F 𝓢) : HasAxiomDummett Γ := ⟨of dummett⟩

end Context

end


protected class LC (𝓢 : S) extends Entailment.Int 𝓢, HasAxiomDummett 𝓢


section

variable [DecidableEq F] [Entailment.LC 𝓢]

open FiniteContext

instance : HasAxiomWLEM 𝓢 where
  wlem {φ} := by
    haveI : 𝓢 ⊢! (φ ➝ ∼φ) ⋎ (∼φ ➝ φ) := dummett;
    apply of_C_of_C_of_A ?_ ?_ this;
    . apply deduct';
      apply A_intro_left;
      apply N_of_CO;
      apply deduct;
      haveI d₁ : [φ, φ ➝ ∼φ] ⊢[𝓢]! φ := FiniteContext.byAxm;
      haveI d₂ : [φ, φ ➝ ∼φ] ⊢[𝓢]! φ ➝ ∼φ := FiniteContext.byAxm;
      have := CO_of_N $ d₂ ⨀ d₁;
      exact this ⨀ d₁;
    . apply deduct';
      apply A_intro_right;
      apply N_of_CO;
      apply deduct;
      haveI d₁ : [∼φ, ∼φ ➝ φ] ⊢[𝓢]! ∼φ := FiniteContext.byAxm;
      haveI d₂ : [∼φ, ∼φ ➝ φ] ⊢[𝓢]! ∼φ ➝ φ := FiniteContext.byAxm;
      haveI := d₂ ⨀ d₁;
      exact (CO_of_N d₁) ⨀ this;

instance : Entailment.KC 𝓢 where

end

end LO.Entailment

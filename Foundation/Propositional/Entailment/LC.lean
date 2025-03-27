import Foundation.Propositional.Entailment.Basic

namespace LO.Entailment

open FiniteContext

variable {S F : Type*} [LogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.LC 𝓢]

instance : HasAxiomWeakLEM 𝓢 where
  wlem φ := by
    haveI : 𝓢 ⊢ (φ ➝ ∼φ) ⋎ (∼φ ➝ φ) := dummett;
    exact χOfCφχOfCψχOfAφψ (by
      apply deduct';
      apply aφψOfφ;
      apply nφOfCφO;
      apply deduct;
      haveI d₁ : [φ, φ ➝ ∼φ] ⊢[𝓢] φ := FiniteContext.byAxm;
      haveI d₂ : [φ, φ ➝ ∼φ] ⊢[𝓢] φ ➝ ∼φ := FiniteContext.byAxm;
      have := cφoOfNφ $ d₂ ⨀ d₁;
      exact this ⨀ d₁;
    ) (by
      apply deduct';
      apply aφψOfψ;
      apply nφOfCφO;
      apply deduct;
      haveI d₁ : [∼φ, ∼φ ➝ φ] ⊢[𝓢] ∼φ := FiniteContext.byAxm;
      haveI d₂ : [∼φ, ∼φ ➝ φ] ⊢[𝓢] ∼φ ➝ φ := FiniteContext.byAxm;
      haveI := d₂ ⨀ d₁;
      exact (cφoOfNφ d₁) ⨀ this;
    ) this;

instance : Entailment.KC 𝓢 where

end LO.Entailment

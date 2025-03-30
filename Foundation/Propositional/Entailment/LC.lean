import Foundation.Propositional.Entailment.Basic

namespace LO.Entailment

open FiniteContext

variable {S F : Type*} [LogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.LC 𝓢]

instance : HasAxiomWeakLEM 𝓢 where
  wlem φ := by
    haveI : 𝓢 ⊢ (φ ➝ ∼φ) ⋎ (∼φ ➝ φ) := dummett;
    exact ofCOfCOfA (by
      apply deduct';
      apply aOfLeft;
      apply nOfCO;
      apply deduct;
      haveI d₁ : [φ, φ ➝ ∼φ] ⊢[𝓢] φ := FiniteContext.byAxm;
      haveI d₂ : [φ, φ ➝ ∼φ] ⊢[𝓢] φ ➝ ∼φ := FiniteContext.byAxm;
      have := cOOfN $ d₂ ⨀ d₁;
      exact this ⨀ d₁;
    ) (by
      apply deduct';
      apply aOfRight;
      apply nOfCO;
      apply deduct;
      haveI d₁ : [∼φ, ∼φ ➝ φ] ⊢[𝓢] ∼φ := FiniteContext.byAxm;
      haveI d₂ : [∼φ, ∼φ ➝ φ] ⊢[𝓢] ∼φ ➝ φ := FiniteContext.byAxm;
      haveI := d₂ ⨀ d₁;
      exact (cOOfN d₁) ⨀ this;
    ) this;

instance : Entailment.KC 𝓢 where

end LO.Entailment

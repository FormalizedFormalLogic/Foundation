import Foundation.Propositional.Entailment.Basic

namespace LO.Entailment

open FiniteContext

variable {S F : Type*} [LogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.LC 𝓢]

instance : HasAxiomWeakLEM 𝓢 where
  wlem φ := by
    haveI : 𝓢 ⊢ (φ ➝ ∼φ) ⋎ (∼φ ➝ φ) := dummett;
    exact or₃''' (by
      apply deduct';
      apply or₁';
      apply neg_equiv'.mpr;
      apply deduct;
      haveI d₁ : [φ, φ ➝ ∼φ] ⊢[𝓢] φ := FiniteContext.byAxm;
      haveI d₂ : [φ, φ ➝ ∼φ] ⊢[𝓢] φ ➝ ∼φ := FiniteContext.byAxm;
      have := neg_equiv'.mp $ d₂ ⨀ d₁;
      exact this ⨀ d₁;
    ) (by
      apply deduct';
      apply or₂';
      apply neg_equiv'.mpr;
      apply deduct;
      haveI d₁ : [∼φ, ∼φ ➝ φ] ⊢[𝓢] ∼φ := FiniteContext.byAxm;
      haveI d₂ : [∼φ, ∼φ ➝ φ] ⊢[𝓢] ∼φ ➝ φ := FiniteContext.byAxm;
      haveI := d₂ ⨀ d₁;
      exact (neg_equiv'.mp d₁) ⨀ this;
    ) this;

instance : Entailment.KC 𝓢 where

end LO.Entailment

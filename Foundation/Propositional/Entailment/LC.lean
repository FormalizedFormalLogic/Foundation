import Foundation.Propositional.Entailment.Basic

namespace LO.Entailment

open FiniteContext

variable {S F : Type*} [LogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.LC 𝓢]

instance : HasAxiomWeakLEM 𝓢 where
  wlem φ := by
    haveI : 𝓢 ⊢ (φ ➝ ∼φ) ⋎ (∼φ ➝ φ) := dummett
    exact of_C_of_C_of_A (by
      apply deduct'
      apply A_intro_left
      apply N_of_CO
      apply deduct
      haveI d₁ : [φ, φ ➝ ∼φ] ⊢[𝓢] φ := FiniteContext.byAxm
      haveI d₂ : [φ, φ ➝ ∼φ] ⊢[𝓢] φ ➝ ∼φ := FiniteContext.byAxm
      have := CO_of_N $ d₂ ⨀ d₁
      exact this ⨀ d₁
    ) (by
      apply deduct'
      apply A_intro_right
      apply N_of_CO
      apply deduct
      haveI d₁ : [∼φ, ∼φ ➝ φ] ⊢[𝓢] ∼φ := FiniteContext.byAxm
      haveI d₂ : [∼φ, ∼φ ➝ φ] ⊢[𝓢] ∼φ ➝ φ := FiniteContext.byAxm
      haveI := d₂ ⨀ d₁
      exact (CO_of_N d₁) ⨀ this
    ) this

instance : Entailment.KC 𝓢 where

end LO.Entailment

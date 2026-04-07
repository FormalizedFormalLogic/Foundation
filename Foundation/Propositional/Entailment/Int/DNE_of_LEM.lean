module
public import Foundation.Propositional.Entailment.Cl.Basic

@[expose] public section

namespace LO.Entailment

variable {S F : Type*} [LogicalConnective F] [DecidableEq F] [Entailment S F]
         {𝓢 : S} [Entailment.Int 𝓢]

open FiniteContext

instance [HasAxiomLEM 𝓢] : HasAxiomDNE 𝓢 where
  dne {φ} := by
    apply deduct';
    exact of_C_of_C_of_A C_id (by
      apply deduct;
      have nnp : [∼φ, ∼∼φ] ⊢[𝓢]! ∼φ 🡒 ⊥ := CO_of_N $ FiniteContext.byAxm;
      have np : [∼φ, ∼∼φ] ⊢[𝓢]! ∼φ := FiniteContext.byAxm;
      exact of_O $ nnp ⨀ np;
    ) $ of lem;

instance [HasAxiomLEM 𝓢] : Entailment.Cl 𝓢 where

end LO.Entailment

end

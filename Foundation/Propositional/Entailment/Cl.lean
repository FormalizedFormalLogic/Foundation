import Foundation.Propositional.Entailment.Basic

namespace LO.Entailment

open FiniteContext

variable {S F : Type*} [LogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.Classical 𝓢]

noncomputable instance : HasAxiomDummett 𝓢 where
  dummett φ ψ := by
    have d₁ : 𝓢 ⊢ φ ➝ ((φ ➝ ψ) ⋎ (ψ ➝ φ)) := cTrans imply₁ or₂;
    have d₂ : 𝓢 ⊢ ∼φ ➝ ((φ ➝ ψ) ⋎ (ψ ➝ φ)) := cTrans efq_imply_not₁ or₁;
    exact ofCOfCOfA d₁ d₂ lem;

noncomputable instance : Entailment.LC 𝓢 where


noncomputable instance : HasAxiomPeirce 𝓢 where
  peirce φ ψ := by
    refine ofCOfCOfA imply₁ ?_ lem;
    apply deduct';
    apply deduct;
    refine (FiniteContext.byAxm (φ := (φ ➝ ψ) ➝ φ)) ⨀ ?_;
    apply deduct;
    apply efq_of_mem_either (by aesop) (by aesop)

end LO.Entailment

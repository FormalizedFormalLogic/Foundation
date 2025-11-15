import Foundation.InterpretabilityLogic.Entailment.CL

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ : F}

/-- Entailment for interpretability logic -/
protected class IL (𝓢 : S) extends InterpretabilityLogic.Entailment.CL 𝓢, HasAxiomJ5 𝓢

variable [Entailment.IL 𝓢]

-- TODO: move
def CNKCN! : 𝓢 ⊢! ∼(φ ⋏ ψ) ➝ (φ ➝ ∼ψ) := by
  apply C_trans CNKANN;
  apply CA_of_C_of_C;
  . apply CNC;
  . apply implyK;

/-- Lemma to prove `ILP ⊢ R` -/
protected def IL.lemma₁ : 𝓢 ⊢! (∼(φ ▷ ∼χ) ⋏ (φ ▷ ψ)) ➝ ◇(ψ ⋏ □χ) := by
  apply CK_of_CC;
  apply C_swap;
  apply deduct';
  apply C_trans ?_ (of INLNM!);
  apply contra;
  suffices [φ ▷ ψ] ⊢[𝓢]! □(ψ ➝ ◇(∼χ)) ➝ φ ▷ ∼χ by
    apply C_trans ?_ this;
    apply of;
    apply box_regularity;
    apply C_trans CNKCN!;
    apply CCC_of_C_right;
    apply C_trans ?_ INLNM!;
    apply contra;
    apply box_regularity;
    apply dne;
  apply deduct;
  apply rhdTrans! ?_ axiomJ5!;
  refine (axiomJ2! (ψ := ψ)) ⨀ ?_ ⨀ ?_
  . apply FiniteContext.byAxm;
    simp;
  . apply rhdOfLC!;
    apply FiniteContext.byAxm;
    simp;

/-- Lemma to prove `ILM ⊢ R` -/
protected def IL.lemma₂ : 𝓢 ⊢! ∼(φ ▷ ∼χ) ➝ ◇(φ ⋏ □χ) := by
  apply deduct';
  refine (of $ IL.lemma₁ (φ := φ)) ⨀ ?_;
  apply K_intro;
  . apply FiniteContext.byAxm;
    simp;
  . apply of;
    apply axiomJ1'!

end LO.InterpretabilityLogic.Entailment

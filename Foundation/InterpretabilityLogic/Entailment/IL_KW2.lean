module

public import Foundation.InterpretabilityLogic.Entailment.IL_W

@[expose] public section

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ : F}

protected class IL_KW2 (𝓢 : S) extends InterpretabilityLogic.Entailment.IL 𝓢, HasAxiomKW2 𝓢

variable [Entailment.IL_KW2 𝓢]

instance «IL(KW2)_⊢_F» : Entailment.HasAxiomF 𝓢 where
  axiomF! {φ} := by
    apply C_trans axiomKW2!;
    apply C_trans axiomJ4!;
    apply C_trans ?_ CNMLN!;
    apply CN_of_CN_right;
    apply deduct';
    refine (K_right $ negEquiv) ⨀ ?_;
    apply deduct;
    haveI H₁ : [◇φ 🡒 ◇(φ ⋏ ∼φ), ◇φ] ⊢[𝓢]! ◇φ 🡒 ◇(φ ⋏ ∼φ) := FiniteContext.nthAxm 0;
    haveI H₂ : [◇φ 🡒 ◇(φ ⋏ ∼φ), ◇φ] ⊢[𝓢]! ◇φ := FiniteContext.nthAxm 1;
    haveI H₃ : [◇φ 🡒 ◇(φ ⋏ ∼φ), ◇φ] ⊢[𝓢]! ◇(φ ⋏ ∼φ) := H₁ ⨀ H₂;
    haveI H₄ : [◇φ 🡒 ◇(φ ⋏ ∼φ), ◇φ] ⊢[𝓢]! ∼◇(φ ⋏ ∼φ) := of $ by
      apply NM!_of_LN!;
      apply nec;
      apply NK_of_ANN;
      apply wlem;
    exact negMDP H₄ H₃;

instance «IL(KW2)_⊢_KW1Zero» : Entailment.HasAxiomKW1Zero 𝓢 where
  axiomKW1Zero! {φ ψ} := by
    apply C_trans axiomKW2!;
    apply R1!;
    apply deduct';
    apply K_intro;
    . apply K_left;
      apply FiniteContext.nthAxm 0;
    . apply A_cases ?_ ?_ $ ANN_of_NK $ K_right $ FiniteContext.nthAxm 0;
      . suffices [ψ, ∼(ψ ⋏ φ)] ⊢[𝓢]! ∼ψ 🡒 ∼φ by tauto;
        apply deduct;
        apply efq_of_mem_either (φ := ψ);
        . simp;
        . simp;
      . apply C_id;

end LO.InterpretabilityLogic.Entailment
end

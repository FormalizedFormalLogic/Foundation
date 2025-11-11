import Foundation.InterpretabilityLogic.Entailment.ILW

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ : F}

protected class IL_KW2 (𝓢 : S) extends InterpretabilityLogic.Entailment.IL 𝓢, HasAxiomKW2 𝓢

variable [Entailment.IL_KW2 𝓢]

def CNMLN! : 𝓢 ⊢! ∼◇φ ➝ □(∼φ) := CN_of_CN_left $ INLNM!

def LN!_of_CMN! (h : 𝓢 ⊢! ∼◇φ) : 𝓢 ⊢! □(∼φ) := CNMLN! ⨀ h

def CLNNM! : 𝓢 ⊢! □(∼φ) ➝ ∼◇φ := CN_of_CN_right $ IMNLN!

def NM!_of_LN! (h : 𝓢 ⊢! □(∼φ)) : 𝓢 ⊢! ∼◇φ := CLNNM! ⨀ h

instance : Entailment.HasAxiomF 𝓢 where
  F! {φ} := by
    apply C_trans KW2!;
    apply C_trans J4!;
    apply C_trans ?_ CNMLN!;
    apply CN_of_CN_right;
    apply deduct';
    refine (K_right $ negEquiv) ⨀ ?_;
    apply deduct;
    haveI H₁ : [◇φ ➝ ◇(φ ⋏ ∼φ), ◇φ] ⊢[𝓢]! ◇φ ➝ ◇(φ ⋏ ∼φ) := FiniteContext.nthAxm 0;
    haveI H₂ : [◇φ ➝ ◇(φ ⋏ ∼φ), ◇φ] ⊢[𝓢]! ◇φ := FiniteContext.nthAxm 1;
    haveI H₃ : [◇φ ➝ ◇(φ ⋏ ∼φ), ◇φ] ⊢[𝓢]! ◇(φ ⋏ ∼φ) := H₁ ⨀ H₂;
    haveI H₄ : [◇φ ➝ ◇(φ ⋏ ∼φ), ◇φ] ⊢[𝓢]! ∼◇(φ ⋏ ∼φ) := of $ by
      apply NM!_of_LN!;
      apply nec;
      apply NK_of_ANN;
      apply wlem;
    exact negMDP H₄ H₃;

end LO.InterpretabilityLogic.Entailment

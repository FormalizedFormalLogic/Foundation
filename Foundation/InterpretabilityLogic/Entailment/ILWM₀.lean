/-
  Visser 1991 (de Jongh), `IL(W, M₀) ⊢ W*`
-/
import Foundation.InterpretabilityLogic.Entailment.ILWStar.Basic
import Foundation.InterpretabilityLogic.Entailment.ILM₀.Basic

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S}

protected class ILWM₀ (𝓢 : S) extends Entailment.ILM₀ 𝓢, Entailment.ILW 𝓢

-- TODO: shorter proof by conjunection of list
variable [LogicalConnective F] [Entailment.Cl 𝓢] in
omit     [InterpretabilityLogicalConnective F] in
section

def K_intro₃ (h₁ : 𝓢 ⊢! φ₁) (h₂ : 𝓢 ⊢! φ₂) (h₃ : 𝓢 ⊢! φ₃) : 𝓢 ⊢! φ₁ ⋏ φ₂ ⋏ φ₃ := by
  apply K_intro;
  . assumption;
  . apply K_intro;
    . assumption;
    . assumption;

def K_assoc : 𝓢 ⊢! (φ ⋏ ψ) ⋏ χ ⭤ φ ⋏ (ψ ⋏ χ) := by
  apply K_intro;
  . apply deduct';
    suffices [φ ⋏ ψ, χ] ⊢[𝓢]! φ ⋏ (ψ ⋏ χ) by tauto;
    apply K_intro₃;
    . apply K_left $ FiniteContext.nthAxm 0;
    . apply K_right $ FiniteContext.nthAxm 0;
    . apply FiniteContext.byAxm; simp;
  . apply deduct';
    suffices [φ, ψ, χ] ⊢[𝓢]! (φ ⋏ ψ) ⋏ χ by tauto;
    apply K_intro
    . apply K_intro <;> . apply FiniteContext.byAxm; simp;
    . apply FiniteContext.byAxm; simp;

def K_assoc_mp : 𝓢 ⊢! (φ ⋏ ψ) ⋏ χ ➝ φ ⋏ (ψ ⋏ χ) := K_left K_assoc
def K_assoc_mpr : 𝓢 ⊢! φ ⋏ (ψ ⋏ χ) ➝ (φ ⋏ ψ) ⋏ χ := K_right K_assoc

end


variable [Entailment.ILWM₀ 𝓢]

instance : HasAxiomWStar 𝓢 := by
  constructor;
  intro φ ψ χ;
  have H₁ : 𝓢 ⊢! (ψ ⋏ □χ) ▷ ((ψ ⋏ □χ ⋏ ◇φ) ⋎ (ψ ⋏ □χ ⋏ □(∼φ))) := by
    apply rhdOfLC!;
    apply nec;
    apply deduct';
    apply of_C_of_C_of_A ?_ ?_ $ show [ψ, □χ] ⊢[𝓢]! □(∼φ) ⋎ ◇φ by
      apply of;
      apply A_replace_right lem;
      apply INLNM!;
    . apply deduct;
      apply A_intro_right;
      apply K_intro₃ <;>
      . apply FiniteContext.byAxm;
        simp;
    . apply deduct;
      apply A_intro_left;
      apply K_intro₃ <;>
      . apply FiniteContext.byAxm;
        simp;
  have H₂ : 𝓢 ⊢! (φ ▷ ψ) ➝ (ψ ⋏ □χ ⋏ ◇φ) ▷ (ψ ⋏ □χ ⋏ □(∼φ)) := by
    apply C_trans $ C_trans axiomW! $ axiomM₀! (χ := χ);
    apply CRhdRhd!_of_C!_C!;
    . apply deduct';
      suffices [ψ, □χ, ◇φ] ⊢[𝓢]! ◇φ ⋏ □χ by tauto;
      apply K_intro <;> . apply FiniteContext.byAxm; simp;
    . apply C_trans K_assoc_mp;
      apply deduct';
      suffices [ψ, □(∼φ), □χ] ⊢[𝓢]! ψ ⋏ □χ ⋏ □(∼φ) by tauto;
      apply K_intro₃ <;> . apply FiniteContext.byAxm; simp;
  apply C_trans H₂ $ axiomJ2Plus! ⨀ H₁;

instance : Entailment.ILWStar 𝓢 where

end LO.InterpretabilityLogic.Entailment

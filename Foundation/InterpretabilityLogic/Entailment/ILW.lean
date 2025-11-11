import Foundation.InterpretabilityLogic.Entailment.IL

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ : F}

protected class ILW (𝓢 : S) extends InterpretabilityLogic.Entailment.IL 𝓢, HasAxiomW 𝓢

-- TODO: move to entailment
variable [LogicalConnective F] [Entailment.Cl 𝓢] in
omit     [InterpretabilityLogicalConnective F] in
def AK_of_KA (h : 𝓢 ⊢! (φ ⋏ (ψ ⋎ χ))) : 𝓢 ⊢! (φ ⋏ ψ ⋎ χ) := by
  apply A_cases ?_ ?_ $ K_right h;
  . apply deduct';
    apply A_intro_left;
    apply K_intro;
    . apply of $ K_left h;
    . apply FiniteContext.byAxm; simp;
  . apply deduct';
    apply A_intro_right;
    apply FiniteContext.byAxm; simp;

variable [Entailment.ILW 𝓢]

def RhdR1! (h : 𝓢 ⊢! ψ ▷ χ) : 𝓢 ⊢! (φ ▷ ψ) ➝ (φ ▷ χ) := by
  apply deduct';
  exact (of axiomJ2!) ⨀ FiniteContext.byAxm ⨀ (of h);

-- TODO: move to entailment
def CKDiaBoxDiaK! : 𝓢 ⊢! ◇φ ⋏ □ψ ➝ ◇(φ ⋏ ψ) := by
  apply C_of_CNN;
  apply C_replace ?_ ?_ $ axiomK (φ := ψ) (ψ := ∼φ);
  . suffices 𝓢 ⊢! □(∼(φ ⋏ ψ)) ➝ □(ψ ➝ ∼φ) by
      apply C_trans ?_ this;
      apply CN_of_CN_left;
      apply INLNM!;
    apply box_regularity;
    apply C_trans CNKANN;
    apply left_A_intro;
    . apply implyK;
    . apply CNC;
  . apply deduct';
    apply NK_of_ANN;
    apply A_symm;
    apply AN_of_C;
    apply deduct;
    suffices [□ψ, □ψ ➝ □(∼φ)] ⊢[𝓢]! □(∼φ) by
      apply C_trans this;
      apply CN_of_CN_right;
      apply IMNLN!;
    exact (FiniteContext.nthAxm 1) ⨀ (FiniteContext.nthAxm 0)

def CRhdRhdA_of_Rhd₁ (h : 𝓢 ⊢! φ ▷ χ) : 𝓢 ⊢! ψ ▷ χ ➝ (φ ⋎ ψ) ▷ χ := axiomJ3! ⨀ h
def CRhdRhdA_of_Rhd₂ (h : 𝓢 ⊢! ψ ▷ χ) : 𝓢 ⊢! φ ▷ χ ➝ (φ ⋎ ψ) ▷ χ := C_swap axiomJ3! ⨀ h

instance : HasAxiomKW2 𝓢 where
  axiomKW2! {φ ψ} := by
    apply C_trans $ axiomW!;
    apply C_trans $ R1! $ CKDiaBoxDiaK!;
    apply C_trans $ RhdR1! $ axiomJ5!;
    apply C_trans $ CRhdRhdA_of_Rhd₁ $ axiomJ1'!;
    apply R2!;
    apply deduct';
    apply AK_of_KA;
    apply K_intro;
    . apply FiniteContext.byAxm; simp;
    . apply A_symm lem;

end LO.InterpretabilityLogic.Entailment

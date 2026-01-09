module
import Foundation.InterpretabilityLogic.Entailment.ILMinus_J4
import Foundation.InterpretabilityLogic.Entailment.ILMinus_J1
import Foundation.Meta.ClProver

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S}

protected class ILMinus_J2 (𝓢 : S) extends Entailment.ILMinus 𝓢, HasAxiomJ2 𝓢

section

variable [Entailment.ILMinus_J2 𝓢]

instance : HasAxiomJ4' 𝓢 := ⟨fun {_ _} ↦ axiomJ2!⟩

def rhdTrans_dhyp! (h₁ : 𝓢 ⊢! ψ ➝ φ ▷ χ) (h₂ : 𝓢 ⊢! ψ ➝ χ ▷ ξ) : 𝓢 ⊢! ψ ➝ φ ▷ ξ := by
  apply deduct';
  exact (of $ axiomJ2!) ⨀ (deductInv' h₁) ⨀ (deductInv' h₂);

end


protected class ILMinus_J2Plus (𝓢 : S) extends Entailment.ILMinus 𝓢, HasAxiomJ2Plus 𝓢

section

variable [Entailment.ILMinus_J2Plus 𝓢]

instance : HasAxiomJ2Plus' 𝓢 := ⟨fun {_ _ _} ↦ C_trans (R1! CAKN!) axiomJ2Plus!⟩

instance : HasAxiomJ2 𝓢 := ⟨fun {_ _ _} ↦ C_trans (R1! or₁) axiomJ2Plus!⟩

end


protected class ILMinus_J2Plus' (𝓢 : S) extends Entailment.ILMinus 𝓢, HasAxiomJ2Plus' 𝓢

section

variable [Entailment.ILMinus_J2Plus' 𝓢]

instance : HasAxiomJ2Plus 𝓢 := ⟨by
  intro A B C;
  dsimp only [Axioms.J2Plus];
  apply deduct';
  have H₁ : [A ▷ (B ⋎ C), A ▷ (B ⋎ C) ➝ B ▷ C] ⊢[𝓢]! ((B ⋎ C) ⋏ ∼C) ▷ C := deductInv $ deductInv' $ CCC_of_C_right $ R2! $ CK_of_CC $ left_A_intro implyK CCN;
  have H₂ : [A ▷ (B ⋎ C), A ▷ (B ⋎ C) ➝ B ▷ C] ⊢[𝓢]! ((B ⋎ C) ⋏ ∼C) ▷ C ➝ A ▷ C := weakening (by simp) $ deductInv' axiomJ2Plus'!;
  have : [A ▷ (B ⋎ C)] ⊢[𝓢]! (A ▷ (B ⋎ C) ➝ B ▷ C) ➝ A ▷ C := deduct $ weakening (by simp) $ H₂ ⨀ H₁;
  apply C_trans implyK this;
⟩

instance : HasAxiomJ4Plus 𝓢 := ⟨by
  intro φ ψ χ;
  apply C_trans $ C_trans ?_ CLNRhd!;
  . exact C_swap $ axiomJ2Plus'!;
  . apply box_regularity CCNKN;
⟩

end



section

variable [Entailment.ILMinus_J1 𝓢] [Entailment.ILMinus_J2 𝓢]

instance : HasAxiomJ2Plus 𝓢 := ⟨by
  intro φ ψ χ;
  apply deduct';
  apply C_trans ?_ $ deductInv' $ axiomJ2!;
  apply of;
  apply C_trans $ axiomJ3! ⨀ axiomJ1'!;
  apply R2!;
  exact inner_A_symm;
⟩

end

instance [Entailment.ILMinus_J2 𝓢] : Entailment.ILMinus_J4' 𝓢 where
instance [Entailment.ILMinus_J2 𝓢] : Entailment.ILMinus_J4 𝓢 where

instance [Entailment.ILMinus_J2Plus 𝓢] : Entailment.ILMinus_J2Plus' 𝓢 where
instance [Entailment.ILMinus_J2Plus' 𝓢] : Entailment.ILMinus_J2Plus 𝓢 where
instance [Entailment.ILMinus_J2Plus 𝓢] : Entailment.ILMinus_J4Plus 𝓢 where

instance [Entailment.ILMinus_J1 𝓢] [Entailment.ILMinus_J2 𝓢] : Entailment.ILMinus_J2Plus 𝓢 where

end LO.InterpretabilityLogic.Entailment

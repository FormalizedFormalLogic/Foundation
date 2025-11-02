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

instance : HasAxiomJ4' 𝓢 := ⟨by
  intro φ ψ;
  apply J2!;
⟩

end


protected class ILMinus_J2Plus (𝓢 : S) extends Entailment.ILMinus 𝓢, HasAxiomJ2Plus 𝓢

section

variable [Entailment.ILMinus_J2Plus 𝓢]

instance : HasAxiomJ2Plus' 𝓢 := ⟨by
  intro φ ψ χ;
  apply sorry
⟩

instance : HasAxiomJ2 𝓢 := ⟨by
  intro φ ψ χ;
  apply C_trans ?_ J2Plus!;
  apply R1!;
  apply or₁;
⟩

end


protected class ILMinus_J2Plus' (𝓢 : S) extends Entailment.ILMinus 𝓢, HasAxiomJ2Plus' 𝓢

section

variable [Entailment.ILMinus_J2Plus' 𝓢]

instance : HasAxiomJ2Plus 𝓢 := ⟨by
  intro φ ψ χ;
  apply sorry;
⟩

instance : HasAxiomJ4Plus 𝓢 := ⟨by
  intro φ ψ χ;
  apply C_trans $ C_trans ?_ CLNRhd!;
  . exact C_swap $ J2Plus'!;
  . apply box_regularity CCNKN;
⟩

end



section

variable [Entailment.ILMinus_J1 𝓢] [Entailment.ILMinus_J2 𝓢]

instance : HasAxiomJ2Plus 𝓢 := ⟨by
  intro φ ψ χ;
  apply deduct';
  apply C_trans ?_ $ deductInv' $ J2!;
  apply of;
  apply C_trans $ J3! ⨀ J1'!;
  apply R2!;
  exact inner_A_symm;
⟩

end

instance [Entailment.ILMinus_J2Plus 𝓢] : Entailment.ILMinus_J2Plus' 𝓢 where
instance [Entailment.ILMinus_J2Plus' 𝓢] : Entailment.ILMinus_J2Plus 𝓢 where
instance [Entailment.ILMinus_J2Plus 𝓢] : Entailment.ILMinus_J4Plus 𝓢 where
instance [Entailment.ILMinus_J1 𝓢] [Entailment.ILMinus_J2 𝓢] : Entailment.ILMinus_J2Plus 𝓢 where

end LO.InterpretabilityLogic.Entailment

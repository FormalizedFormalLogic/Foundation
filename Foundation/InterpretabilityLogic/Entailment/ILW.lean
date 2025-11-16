import Foundation.InterpretabilityLogic.Entailment.IL

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ : F}

protected class ILW (𝓢 : S) extends InterpretabilityLogic.Entailment.IL 𝓢, HasAxiomW 𝓢

variable [Entailment.ILW 𝓢]

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

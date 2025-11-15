import Foundation.InterpretabilityLogic.Entailment.ILRStar
import Foundation.InterpretabilityLogic.Entailment.ILMinus_M

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ : F}

/-- Entailment for interpretability logic with Montagna's principle -/
protected class ILM (𝓢 : S) extends InterpretabilityLogic.Entailment.IL 𝓢, HasAxiomM 𝓢

variable [Entailment.ILM 𝓢]

instance : Entailment.ILMinus_M 𝓢 where

instance : Entailment.HasAxiomW 𝓢 where
  axiomW! {φ ψ} := by
    dsimp [Axioms.W];
    apply C_trans $ axiomM! (χ := (∼φ));
    apply R2!;
    sorry;

instance : Entailment.HasAxiomR 𝓢 where
  axiomR! {φ ψ χ} := by
    apply deduct';
    apply rhdTrans! (of $ rhdOfLC! $ nec $ oh);
    apply rhdTrans! (of $ axiomJ5!);
    apply axiomM!;

end LO.InterpretabilityLogic.Entailment

import Foundation.InterpretabilityLogic.Entailment.IL
import Foundation.InterpretabilityLogic.Entailment.ILRStar
import Foundation.InterpretabilityLogic.Entailment.ILMinus_J4

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ : F}

/-- Entailment for interpretability logic with persistence principle -/
protected class ILP (𝓢 : S) extends InterpretabilityLogic.Entailment.IL 𝓢, HasAxiomP 𝓢

variable [Entailment.ILP 𝓢]

instance : Entailment.HasAxiomR 𝓢 where
  axiomR! {φ ψ χ} := by
    apply deduct';
    apply rhdTrans! $ show [φ ▷ ψ] ⊢[𝓢]! ∼(φ ▷ ∼χ) ▷ (∼(φ ▷ ∼χ) ⋏ (φ ▷ ψ)) by
      apply rhdOfLC!;
      apply C_trans axiomP!;
      apply box_regularity;
      apply C_swap;
      apply CC_of_CK;
      apply C_id;
    apply rhdTrans! $ show [φ ▷ ψ] ⊢[𝓢]! (∼(φ ▷ ∼χ) ⋏ (φ ▷ ψ)) ▷ ◇(ψ ⋏ □χ) by
      apply of;
      apply rhdOfLC!
      apply nec;
      apply IL.lemma₁;
    apply axiomJ5!;

end LO.InterpretabilityLogic.Entailment

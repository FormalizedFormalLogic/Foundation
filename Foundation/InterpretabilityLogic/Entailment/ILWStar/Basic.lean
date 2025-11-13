import Foundation.InterpretabilityLogic.Entailment.ILW

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ ξ : F}

protected class ILWStar (𝓢 : S) extends InterpretabilityLogic.Entailment.IL 𝓢, HasAxiomWStar 𝓢

variable [Entailment.ILWStar 𝓢]

instance : Entailment.HasAxiomW 𝓢 := by
  constructor;
  intro φ ψ;
  apply rhdTrans_dhyp! (χ := ψ ⋏ □⊤) ?_ ?_;
  . show 𝓢 ⊢! φ ▷ ψ ➝ φ ▷ (ψ ⋏ □⊤);
    apply R1!;
    apply deduct';
    apply K_intro;
    . apply FiniteContext.byAxm; simp;
    . apply axiomN;
  . show 𝓢 ⊢! φ ▷ ψ ➝ (ψ ⋏ □⊤) ▷ (ψ ⋏ □(∼φ));
    apply C_trans axiomWStar!;
    apply R1!;
    apply deduct';
    suffices [ψ, □⊤, □(∼φ)] ⊢[𝓢]! ψ ⋏ □(∼φ) by tauto;
    apply K_intro <;>
    . apply FiniteContext.byAxm;
      simp;
instance : Entailment.ILW 𝓢 where

end LO.InterpretabilityLogic.Entailment

import Foundation.InterpretabilityLogic.Entailment.ILR
import Foundation.InterpretabilityLogic.Entailment.ILW
import Foundation.InterpretabilityLogic.Entailment.ILWM₀

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ : F}

protected class ILRW (𝓢 : S) extends InterpretabilityLogic.Entailment.ILR 𝓢, InterpretabilityLogic.Entailment.ILW 𝓢

variable [Entailment.ILRW 𝓢]

instance : HasAxiomRStar 𝓢 where
  axiomRStar! {φ ψ χ} := by
    apply C_trans axiomW!;
    apply C_trans $ axiomR! (χ := χ);
    apply R1!;
    apply C_trans K_assoc_mp;
    suffices [ψ, □(∼φ), □χ] ⊢[𝓢]! ψ ⋏ □χ ⋏ □(∼φ) by tauto;
    apply K_intro₃ <;>
    . apply FiniteContext.byAxm;
      simp;

end LO.InterpretabilityLogic.Entailment

import Foundation.InterpretabilityLogic.Entailment.IL_R
import Foundation.InterpretabilityLogic.Entailment.IL_W
import Foundation.InterpretabilityLogic.Entailment.IL_M₀_W

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ : F}

protected class IL_R_W (𝓢 : S) extends InterpretabilityLogic.Entailment.IL_R 𝓢, InterpretabilityLogic.Entailment.IL_W 𝓢

variable [Entailment.IL_R_W 𝓢]

/--
  E. Goris & J. Joosten 2011, Lemma 4.5
-/
instance : HasAxiomRstar 𝓢 where
  axiomRstar! {φ ψ χ} := by
    apply C_trans axiomW!;
    apply C_trans $ axiomR! (χ := χ);
    apply R1!;
    apply C_trans K_assoc_mp;
    suffices [ψ, □(∼φ), □χ] ⊢[𝓢]! ψ ⋏ □χ ⋏ □(∼φ) by tauto;
    apply K_intro₃ <;>
    . apply FiniteContext.byAxm;
      simp;

end LO.InterpretabilityLogic.Entailment

module

public import Foundation.InterpretabilityLogic.Entailment.IL


@[expose] public section

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ : F}

protected class IL_R (𝓢 : S) extends InterpretabilityLogic.Entailment.IL 𝓢, HasAxiomR 𝓢

variable [Entailment.IL_R 𝓢]

instance IL_R_proves_axiomM₀ : Entailment.HasAxiomM₀ 𝓢 where
  axiomM₀! := by
    intro φ ψ χ;
    apply rhdTrans_dhyp! ?_ axiomR!;
    apply dhyp;
    apply rhdOfLC!;
    apply nec;
    apply CN_of_CN_right;
    apply C_trans axiomJ4!;
    apply C_trans ?_ CCNNK!;
    apply CCC!_of_C!;
    apply CMNNL!;

/--
  E. Goris & J. J. Joosten 2011, Lemma 4.4
-/
instance IL_R_proves_axiomP₀ : Entailment.HasAxiomP₀ 𝓢 where
  axiomP₀! := by
    intro φ ψ;
    apply C_trans $ axiomR! (χ := ∼ψ);
    apply C_trans ?_ CRhdNOL!;
    apply CRhdRhd!_of_C!_C!;
    . apply contra;
      apply R1!;
      apply dne;
    . apply deduct';
      suffices [◇ψ, □(∼ψ)] ⊢[𝓢]! ⊥ by tauto;
      have H₁ : [◇ψ, □(∼ψ)] ⊢[𝓢]! ∼(□(∼ψ)) := (of IMNLN!) ⨀ (FiniteContext.nthAxm 0);
      have H₂ : [◇ψ, □(∼ψ)] ⊢[𝓢]! □(∼ψ) := FiniteContext.nthAxm 1;
      apply negMDP H₁ H₂;

end LO.InterpretabilityLogic.Entailment
end

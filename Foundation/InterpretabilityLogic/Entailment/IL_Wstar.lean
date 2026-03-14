module

public import Foundation.InterpretabilityLogic.Entailment.IL_W

@[expose] public section

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ ξ : F}

protected class IL_Wstar (𝓢 : S) extends InterpretabilityLogic.Entailment.IL 𝓢, HasAxiomWstar 𝓢

variable [Entailment.IL_Wstar 𝓢]

instance : Entailment.HasAxiomW 𝓢 := by
  constructor;
  intro φ ψ;
  apply rhdTrans_dhyp! (χ := ψ ⋏ □⊤) ?_ ?_;
  . show 𝓢 ⊢! φ ▷ ψ 🡒 φ ▷ (ψ ⋏ □⊤);
    apply R1!;
    apply deduct';
    apply K_intro;
    . apply FiniteContext.byAxm; simp;
    . apply axiomN;
  . show 𝓢 ⊢! φ ▷ ψ 🡒 (ψ ⋏ □⊤) ▷ (ψ ⋏ □(∼φ));
    apply C_trans axiomWstar!;
    apply R1!;
    apply deduct';
    suffices [ψ, □⊤, □(∼φ)] ⊢[𝓢]! ψ ⋏ □(∼φ) by tauto;
    apply K_intro <;>
    . apply FiniteContext.byAxm;
      simp;

instance : Entailment.HasAxiomM₀ 𝓢 := by
  constructor;
  intro φ ψ χ;
  apply C_trans $ show 𝓢 ⊢! (φ ▷ ψ) 🡒 (φ ▷ (ψ ⋎ ◇φ)) by
    apply R1!;
    apply or₁;
  apply C_trans $ axiomWstar! (χ := χ);

  have : 𝓢 ⊢! ((ψ ⋎ ◇φ) ⋏ □χ) ▷ (ψ ⋏ □χ) 🡒 (◇φ ⋏ □χ) ▷ (ψ ⋏ □χ) := axiomJ2! ⨀ (rhdOfLC! $ nec $ CKK_of_C or₂);
  apply C_trans ?_ this;
  apply R1!;
  apply deduct';
  suffices [(ψ ⋎ ◇φ), □χ, □(∼φ)] ⊢[𝓢]! ψ ⋏ □χ by tauto;
  apply K_intro;
  . apply of_C_of_C_of_A ?_ ?_ (FiniteContext.nthAxm 0);
    . apply C_id;
    . apply deduct;
      apply of_O;
      apply negMDP (φ := □(∼φ));
      . exact (of $ IMNLN!) ⨀ FiniteContext.byAxm
      . apply FiniteContext.byAxm;
        simp;
  . apply FiniteContext.byAxm;
    simp;

end LO.InterpretabilityLogic.Entailment
end

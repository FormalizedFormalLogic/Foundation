module

/-
  Visser 1991 (de Jongh), `IL(W, M₀) ⊢ W*`
-/
public import Foundation.InterpretabilityLogic.Entailment.IL_Wstar
public import Foundation.InterpretabilityLogic.Entailment.IL_M₀

@[expose] public section

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S}

protected class IL_M₀_W (𝓢 : S) extends Entailment.IL_M₀ 𝓢, Entailment.IL_W 𝓢

variable [Entailment.IL_M₀_W 𝓢]

instance : HasAxiomWstar 𝓢 := by
  constructor;
  intro φ ψ χ;
  have H₁ : 𝓢 ⊢! (ψ ⋏ □χ) ▷ ((ψ ⋏ □χ ⋏ ◇φ) ⋎ (ψ ⋏ □χ ⋏ □(∼φ))) := by
    apply rhdOfLC!;
    apply nec;
    apply deduct';
    apply of_C_of_C_of_A ?_ ?_ $ show [ψ, □χ] ⊢[𝓢]! □(∼φ) ⋎ ◇φ by
      apply of;
      apply A_replace_right lem;
      apply INLNM!;
    . apply deduct;
      apply A_intro_right;
      apply K_intro₃ <;>
      . apply FiniteContext.byAxm;
        simp;
    . apply deduct;
      apply A_intro_left;
      apply K_intro₃ <;>
      . apply FiniteContext.byAxm;
        simp;
  have H₂ : 𝓢 ⊢! (φ ▷ ψ) 🡒 (ψ ⋏ □χ ⋏ ◇φ) ▷ (ψ ⋏ □χ ⋏ □(∼φ)) := by
    apply C_trans $ C_trans axiomW! $ axiomM₀! (χ := χ);
    apply CRhdRhd!_of_C!_C!;
    . apply deduct';
      suffices [ψ, □χ, ◇φ] ⊢[𝓢]! ◇φ ⋏ □χ by tauto;
      apply K_intro <;> . apply FiniteContext.byAxm; simp;
    . apply C_trans K_assoc_mp;
      apply deduct';
      suffices [ψ, □(∼φ), □χ] ⊢[𝓢]! ψ ⋏ □χ ⋏ □(∼φ) by tauto;
      apply K_intro₃ <;> . apply FiniteContext.byAxm; simp;
  apply C_trans H₂ $ axiomJ2Plus! ⨀ H₁;


end LO.InterpretabilityLogic.Entailment
end

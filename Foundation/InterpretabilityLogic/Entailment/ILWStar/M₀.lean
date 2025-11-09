/-
  Visser 1991, `IL(W*) ⊢ M₀` (`IL⁻(J1, J2) ⊢ M₀`)
-/
import Foundation.InterpretabilityLogic.Entailment.ILWStar.Basic
import Foundation.InterpretabilityLogic.Entailment.ILM₀.Basic

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S}
  [Entailment.ILWStar 𝓢]

instance : HasAxiomM₀ 𝓢 := by
  constructor;
  intro φ ψ χ;
  apply C_trans $ show 𝓢 ⊢! (φ ▷ ψ) ➝ (φ ▷ (ψ ⋎ ◇φ)) by
    apply R1!;
    apply or₁;
  apply C_trans $ WStar! (χ := χ);

  have : 𝓢 ⊢! ((ψ ⋎ ◇φ) ⋏ □χ) ▷ (ψ ⋏ □χ) ➝ (◇φ ⋏ □χ) ▷ (ψ ⋏ □χ) := J2! ⨀ (rhdOfLC! $ nec $ CKK_of_C or₂);
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
instance : Entailment.ILM₀ 𝓢 where

end LO.InterpretabilityLogic.Entailment

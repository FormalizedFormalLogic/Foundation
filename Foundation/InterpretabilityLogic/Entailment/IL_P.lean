module

public import Foundation.InterpretabilityLogic.Entailment.IL_Rstar

@[expose] public section

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ : F}

/-- Entailment for interpretability logic with persistence principle -/
protected class IL_P (𝓢 : S) extends InterpretabilityLogic.Entailment.IL 𝓢, HasAxiomP 𝓢

variable [Entailment.IL_P 𝓢]

instance «IL(P)_⊢_R» : Entailment.HasAxiomR 𝓢 where
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


def RIIPRC : 𝓢 ⊢! φ ▷ ψ 🡒 □(◇φ 🡒 ◇ψ) := by
  apply deduct';
  refine of (box_regularity $ axiomJ4!) ⨀ axiomP!;

instance «IL(P)_⊢_W» : Entailment.HasAxiomW 𝓢 where
  axiomW! {φ ψ} := by
    apply deduct';
    suffices [φ ▷ ψ] ⊢[𝓢]! (ψ ⋏ ◇φ) ▷ (ψ ⋏ □(∼φ)) by
      apply axiomJ2Plus! ⨀ ?_ ⨀ this;
      show [φ ▷ ψ] ⊢[𝓢]! φ ▷ ((ψ ⋏ ◇φ) ⋎ (ψ ⋏ □(∼φ)));
      apply rhdTrans! $ FiniteContext.nthAxm 0;
      apply of;
      apply rhdOfLC!;
      apply nec;
      apply CAKK_of_A;
      apply A_symm;
      apply A_replace_right lem INLNM!;
    apply rhdTrans! $ show [φ ▷ ψ] ⊢[𝓢]! (ψ ⋏ ◇φ) ▷ ◇ψ by
      suffices 𝓢 ⊢! □(ψ ⋏ ◇φ 🡒 ◇ψ) 🡒 (ψ ⋏ ◇φ) ▷ ◇ψ by
        apply C_trans ?_ this;
        apply C_trans axiomP!;
        apply box_regularity;
        apply C_swap;
        apply deduct';
        apply C_trans axiomJ4!;
        apply deduct;
        exact (FiniteContext.nthAxm 0) ⨀ (K_right $ FiniteContext.nthAxm 1);
      apply deduct';
      apply rhdOfLC!;
      apply FiniteContext.byAxm;
      simp;
    apply rhdTrans! $ of M_rhd_MALN;
    apply rhdTrans! $ axiomJ5!;

    show [φ ▷ ψ] ⊢[𝓢]! (ψ ⋏ □(∼ψ)) ▷ (ψ ⋏ □(∼φ));
    apply C_trans ?_ replace_Rhd_K_right;
    apply C_trans $ RIIPRC;
    apply box_regularity;
    apply deduct';
    apply C_of_CNN;
    apply C_replace (of INLNM!) (of IMNLN!);
    apply FiniteContext.byAxm;
    simp;

end LO.InterpretabilityLogic.Entailment
end

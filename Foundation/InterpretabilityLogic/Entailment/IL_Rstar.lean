module

public import Foundation.InterpretabilityLogic.Entailment.IL_R
public import Foundation.InterpretabilityLogic.Entailment.IL_M₀_W

@[expose] public section

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ : F}

protected class IL_Rstar (𝓢 : S) extends InterpretabilityLogic.Entailment.IL 𝓢, Entailment.HasAxiomRstar 𝓢

variable [Entailment.IL_Rstar 𝓢]

instance : HasAxiomR 𝓢 where
  axiomR! {φ ψ χ} := by
    apply C_trans $ axiomRstar! (χ := χ);
    apply R1!;
    apply C_trans K_assoc_mpr;
    apply and₁;

instance : Entailment.IL_R 𝓢 where

/--
  E. Goris & J. Joosten 2011, Lemma 4.5
-/
instance : HasAxiomW 𝓢 where
  axiomW! {φ ψ} := by
    dsimp [Axioms.W];
    have H₁ : 𝓢 ⊢! (φ ▷ ψ) ➝ ◇φ ▷ (ψ ⋏ □(∼φ)) := by
      apply C_trans $ axiomRstar! (χ := ⊤);
      apply CRhdRhd!_of_C!_C!;
      . apply C_trans IMNLN!;
        apply contra;
        apply C_trans ?_ CRhdNOL!;
        apply CRhdRhd!_of_C!_C! dne CNTO;
      . suffices [ψ, □⊤, □(∼φ)] ⊢[𝓢]! ψ ⋏ □(∼φ) by tauto;
        apply K_intro <;> . apply FiniteContext.byAxm; simp;
    have H₂ : 𝓢 ⊢! (φ ▷ ψ) ➝ ((ψ ⋏ □(∼φ)) ⋎ ◇φ) ▷ (ψ ⋏ □(∼φ)) := by
      apply (of axiomJ3!) ⨀ axiomJ1'! ⨀ (deductInv' H₁);
    have H₃ : 𝓢 ⊢! (φ ▷ ψ) ➝ φ ▷ ((ψ ⋏ □(∼φ)) ⋎ ◇φ) := by
      apply R1!;
      apply deduct';
      apply A_cases ?_ ?_ $ lem (φ := □(∼φ));
      . apply deduct;
        apply A_intro_left;
        apply K_intro <;> . apply FiniteContext.byAxm; simp;
      . apply deduct;
        apply A_intro_right;
        refine (of INLNM!) ⨀ ?_;
        apply FiniteContext.byAxm;
        simp
    apply (of axiomJ2!) ⨀ (deductInv' H₃) ⨀ (deductInv' H₂);

instance : Entailment.IL_W 𝓢 where


end LO.InterpretabilityLogic.Entailment
end

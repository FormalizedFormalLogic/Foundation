module

public import Foundation.InterpretabilityLogic.Entailment.CL

@[expose] public section

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ : F}

/-- Entailment for interpretability logic -/
protected class IL (𝓢 : S) extends InterpretabilityLogic.Entailment.CL 𝓢, HasAxiomJ5 𝓢

variable [Entailment.IL 𝓢]

def RhdR1! (h : 𝓢 ⊢! ψ ▷ χ) : 𝓢 ⊢! (φ ▷ ψ) 🡒 (φ ▷ χ) := by
  apply deduct';
  exact (of axiomJ2!) ⨀ FiniteContext.byAxm ⨀ (of h);

def CRhdRhdA_of_Rhd₁ (h : 𝓢 ⊢! φ ▷ χ) : 𝓢 ⊢! ψ ▷ χ 🡒 (φ ⋎ ψ) ▷ χ := axiomJ3! ⨀ h
def CRhdRhdA_of_Rhd₂ (h : 𝓢 ⊢! ψ ▷ χ) : 𝓢 ⊢! φ ▷ χ 🡒 (φ ⋎ ψ) ▷ χ := C_swap axiomJ3! ⨀ h

def replace_Rhd_K_right : 𝓢 ⊢! □(ψ₁ 🡒 ψ₂) 🡒 (φ ⋏ ψ₁) ▷ (φ ⋏ ψ₂) := by
  suffices 𝓢 ⊢! □(φ ⋏ ψ₁ 🡒 φ ⋏ ψ₂) 🡒 (φ ⋏ ψ₁) ▷ (φ ⋏ ψ₂) by
    apply C_trans ?_ this;
    apply box_regularity;
    apply deduct';
    apply CKK_of_C';
    apply FiniteContext.byAxm;
    simp;
  apply deduct';
  apply rhdOfLC!;
  apply FiniteContext.byAxm;
  simp;

def M_rhd_MALN : 𝓢 ⊢! ◇ψ ▷ ◇(ψ ⋏ □(∼ψ)) := by
  apply rhdOfLC!;
  apply nec;
  apply C_replace IMNLN! INLNM!;
  apply contra;
  apply C_trans ?_ axiomL;
  apply box_regularity;
  apply C_trans CNKCN!;
  apply CCNCN;

/-- Lemma to prove `IL_P ⊢ R` -/
protected def IL.lemma₁ : 𝓢 ⊢! (∼(φ ▷ ∼χ) ⋏ (φ ▷ ψ)) 🡒 ◇(ψ ⋏ □χ) := by
  apply CK_of_CC;
  apply C_swap;
  apply deduct';
  apply C_trans ?_ (of INLNM!);
  apply contra;
  suffices [φ ▷ ψ] ⊢[𝓢]! □(ψ 🡒 ◇(∼χ)) 🡒 φ ▷ ∼χ by
    apply C_trans ?_ this;
    apply of;
    apply box_regularity;
    apply C_trans CNKCN!;
    apply CCC_of_C_right;
    apply C_trans ?_ INLNM!;
    apply contra;
    apply box_regularity;
    apply dne;
  apply deduct;
  apply rhdTrans! ?_ axiomJ5!;
  refine (axiomJ2! (ψ := ψ)) ⨀ ?_ ⨀ ?_
  . apply FiniteContext.byAxm;
    simp;
  . apply rhdOfLC!;
    apply FiniteContext.byAxm;
    simp;

/-- Lemma to prove `ILM ⊢ R` -/
protected def IL.lemma₂ : 𝓢 ⊢! ∼(φ ▷ ∼χ) 🡒 ◇(φ ⋏ □χ) := by
  apply deduct';
  refine (of $ IL.lemma₁ (φ := φ)) ⨀ ?_;
  apply K_intro;
  . apply FiniteContext.byAxm;
    simp;
  . apply of;
    apply axiomJ1'!

end LO.InterpretabilityLogic.Entailment
end

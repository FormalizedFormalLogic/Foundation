module

public import Foundation.InterpretabilityLogic.Entailment.ILMinus_J2

@[expose] public section

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ : F}

/-- Entailment for conservatibity logic -/
protected class CL (𝓢 : S) extends Modal.Entailment.GL 𝓢, HasAxiomJ1 𝓢, HasAxiomJ2 𝓢, HasAxiomJ3 𝓢, HasAxiomJ4 𝓢

variable [Entailment.CL 𝓢]

instance : HasAxiomJ6 𝓢 := ⟨by
  intro φ;
  apply Entailment.K_intro;
  . apply C_trans ?_ axiomJ1!;
    apply box_regularity;
    exact CCNO!;
  . apply C_trans axiomJ4!;
    apply C_trans CCCNN;
    apply deduct';
    haveI H₁ : [∼◇⊥ 🡒 ∼◇(∼φ)] ⊢[𝓢]! ∼◇⊥ 🡒 ∼◇(∼φ) := FiniteContext.byAxm $ by simp;
    haveI H₂ : [∼◇⊥ 🡒 ∼◇(∼φ)] ⊢[𝓢]! ∼◇⊥ := of $ NMO!
    haveI H₃ : [∼◇⊥ 🡒 ∼◇(∼φ)] ⊢[𝓢]! ∼◇(∼φ) := H₁ ⨀ H₂;
    haveI H₄ : [∼◇⊥ 🡒 ∼◇(∼φ)] ⊢[𝓢]! ∼◇(∼φ) 🡒 □φ := of INMNL!;
    apply H₄ ⨀ H₃;
⟩

instance : HasAxiomJ4Plus 𝓢 := ⟨λ {_ _ _} ↦ C_trans axiomJ1! (C_swap axiomJ2!)⟩

instance : HasRule1 𝓢 := ⟨λ {_ _ _} hφ ↦ axiomJ4Plus! ⨀ nec hφ⟩

def CLCCRhdRhd! : 𝓢 ⊢! □(φ 🡒 ψ) 🡒 (ψ ▷ χ 🡒 φ ▷ χ) := C_trans axiomJ1! axiomJ2!

instance : HasRule2 𝓢 := ⟨λ {_ _ _} hφ ↦ CLCCRhdRhd! ⨀ nec hφ⟩

instance : Entailment.ILMinus_J1 𝓢 where
instance : Entailment.ILMinus_J2 𝓢 where

end LO.InterpretabilityLogic.Entailment
end

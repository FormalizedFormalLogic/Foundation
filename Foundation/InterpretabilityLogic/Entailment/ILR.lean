import Foundation.InterpretabilityLogic.Entailment.IL


namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ : F}

/-- Entailment for interpretability logic with persistence principle -/
protected class ILR (𝓢 : S) extends InterpretabilityLogic.Entailment.IL 𝓢, HasAxiomR 𝓢

variable [Entailment.ILR 𝓢]

def CCNNK! : 𝓢 ⊢! (φ ➝ ∼ψ) ➝ ∼(φ ⋏ ψ):= C_replace CCAN CANNNK C_id

def CCC!_of_C! (h : 𝓢 ⊢! φ₂ ➝ ψ₂) : 𝓢 ⊢! (φ ➝ φ₂) ➝ (φ ➝ ψ₂) := CCC!_of_C!_of_C! C_id h

def CMNNL! : 𝓢 ⊢! ◇(∼φ) ➝ (∼□φ) := by
  apply C_trans IMNLN!;
  apply contra;
  apply box_regularity;
  apply dni;

instance : Entailment.HasAxiomM₀ 𝓢 where
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

instance : Entailment.HasAxiomP₀ 𝓢 where
  axiomP₀! := by
    intro φ ψ;
    have := axiomR! (𝓢 := 𝓢) (φ := φ) (ψ := ψ) (χ := ∼ψ);
    dsimp [Axioms.R, Axioms.P₀] at this ⊢;
    sorry;

end LO.InterpretabilityLogic.Entailment

import Foundation.InterpretabilityLogic.Entailment.IL

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ : F}

/-- Entailment for interpretability logic with Montagna's principle -/
protected class ILM (𝓢 : S) extends InterpretabilityLogic.Entailment.IL 𝓢, HasAxiomM 𝓢

variable [Entailment.ILM 𝓢]

-- TODO: move to Entailment
def replace_CK_left (h₁ : 𝓢 ⊢! φ₂ ➝ φ₁) (h₂ : 𝓢 ⊢! φ₁ ⋏ ψ ➝ χ) : 𝓢 ⊢! φ₂ ⋏ ψ ➝ χ := by
  apply C_trans ?_ h₂;
  apply CKK_of_C h₁;

-- TODO: move to Entailment
def replace_CK_right (h₁ : 𝓢 ⊢! ψ₁ ➝ ψ₂) (h₂ : 𝓢 ⊢! φ ⋏ ψ₂ ➝ χ) : 𝓢 ⊢! φ ⋏ ψ₁ ➝ χ := by
  apply C_trans ?_ h₂;
  apply CKK_of_C' h₁;

-- TODO: move to Entailment
def left_K_symm (d : 𝓢 ⊢! φ ⋏ ψ ➝ χ) : 𝓢 ⊢! ψ ⋏ φ ➝ χ := C_trans (CKK _ _) d

instance : HasAxiomKM1 𝓢 := ⟨by
  intro φ ψ;
  apply C_trans $ M! (χ := ∼ψ);
  apply C_trans $ show 𝓢 ⊢! ((φ ⋏ □(∼ψ)) ▷ (◇ψ ⋏ □(∼ψ))) ➝ ((φ ⋏ □(∼ψ)) ▷ ⊥) by
    apply R1!;
    apply replace_CK_left IMNLN!;
    apply left_K_symm;
    apply CKNO;
  apply C_trans CRhdOLN!;
  apply box_regularity;
  apply C_trans CNKANN;
  apply left_A_intro;
  . apply CNC;
  . apply C_swap;
    apply deduct';
    apply of;
    apply INLNM!;
⟩

end LO.InterpretabilityLogic.Entailment

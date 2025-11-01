import Foundation.InterpretabilityLogic.Entailment.Basic
import Foundation.Modal.Entailment.GL

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ φ₁ φ₂ ψ ψ₁ ψ₂ χ : F}

protected class ILMinus (𝓢 : S) extends Modal.Entailment.GL 𝓢, HasAxiomJ3 𝓢, HasAxiomJ6 𝓢, HasRule1 𝓢, HasRule2 𝓢

variable [Entailment.ILMinus 𝓢]

def CRhdRhd!_of_C!_C! (hφ : 𝓢 ⊢! φ₁ ➝ φ₂) (hψ : 𝓢 ⊢! ψ₁ ➝ ψ₂) : 𝓢 ⊢! (φ₁ ▷ ψ₁) ➝ (φ₂ ▷ ψ₂) := by
  apply C_trans;
  . apply R2! hφ;
  . apply R1! hψ;

omit [DecidableEq F] in
@[grind] lemma CRhdRhd_of_C_C : 𝓢 ⊢ φ₁ ➝ φ₂ → 𝓢 ⊢ ψ₁ ➝ ψ₂ → 𝓢 ⊢ (φ₁ ▷ ψ₁) ➝ (φ₂ ▷ ψ₂) := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨CRhdRhd!_of_C!_C! h₁ h₂⟩



def ERhdRhd!_of_E!_E! (hφ : 𝓢 ⊢! φ₁ ⭤ φ₂) (hψ : 𝓢 ⊢! ψ₁ ⭤ ψ₂) : 𝓢 ⊢! (φ₁ ▷ ψ₁) ⭤ (φ₂ ▷ ψ₂) := by
  apply K_intro;
  . apply CRhdRhd!_of_C!_C! (K_left hφ) (K_left hψ);
  . apply CRhdRhd!_of_C!_C! (K_right hφ) (K_right hψ);

omit [DecidableEq F] in
@[grind]
lemma ERhdRhd_of_E_E : 𝓢 ⊢ φ₁ ⭤ φ₂ → 𝓢 ⊢ ψ₁ ⭤ ψ₂ → 𝓢 ⊢ (φ₁ ▷ ψ₁) ⭤ (φ₂ ▷ ψ₂) := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ERhdRhd!_of_E!_E! h₁ h₂⟩

def CLNRhd! : 𝓢 ⊢! □(∼φ) ➝ (φ ▷ ψ) := by
  apply C_trans CLRhdNO!;
  apply CRhdRhd!_of_C!_C!;
  . apply dne;
  . apply efq;
@[simp, grind] lemma CLNRhd : 𝓢 ⊢ □(∼φ) ➝ (φ ▷ ψ) := ⟨CLNRhd!⟩

def CCRhdRhdLC! : 𝓢 ⊢! □(φ ➝ ψ) ➝ (ψ ▷ χ ➝ φ ▷ χ) := by
  suffices 𝓢 ⊢! □(∼(φ ⋏ ∼ψ)) ➝ ψ ▷ χ ➝ φ ▷ χ by sorry;
  have H₁ : 𝓢 ⊢! □(∼(φ ⋏ ∼ψ)) ➝ (φ ⋏ ∼ψ) ▷ χ := CLNRhd!;
  have H₂ : 𝓢 ⊢! (φ ⋏ ∼ψ) ▷ χ ➝ ψ ▷ χ ➝ ((φ ⋏ ∼ψ) ⋎ ψ) ▷ χ := J3!
  apply C_trans H₁;
  sorry;

end LO.InterpretabilityLogic.Entailment

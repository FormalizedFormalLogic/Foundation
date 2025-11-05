import Foundation.InterpretabilityLogic.Entailment.Basic
import Foundation.Modal.Entailment.GL
import Foundation.Meta.ClProver

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ φ₁ φ₂ ψ ψ₁ ψ₂ χ : F}

protected class ILMinus (𝓢 : S) extends Modal.Entailment.GL 𝓢, HasAxiomJ3 𝓢, HasAxiomJ6 𝓢, HasRule1 𝓢, HasRule2 𝓢

variable [Entailment.ILMinus 𝓢]

def CRhdRhd!_of_C!_C! (hφ : 𝓢 ⊢! φ₂ ➝ φ₁) (hψ : 𝓢 ⊢! ψ₁ ➝ ψ₂) : 𝓢 ⊢! (φ₁ ▷ ψ₁) ➝ (φ₂ ▷ ψ₂) := by
  apply C_trans;
  . apply R1!; apply hψ;
  . apply R2!; apply hφ;

omit [DecidableEq F] in
@[grind] lemma CRhdRhd_of_C_C : 𝓢 ⊢ φ₂ ➝ φ₁ → 𝓢 ⊢ ψ₁ ➝ ψ₂ → 𝓢 ⊢ (φ₁ ▷ ψ₁) ➝ (φ₂ ▷ ψ₂) := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨CRhdRhd!_of_C!_C! h₁ h₂⟩



def ERhdRhd!_of_E!_E! (hφ : 𝓢 ⊢! φ₁ ⭤ φ₂) (hψ : 𝓢 ⊢! ψ₁ ⭤ ψ₂) : 𝓢 ⊢! (φ₁ ▷ ψ₁) ⭤ (φ₂ ▷ ψ₂) := by
  apply K_intro;
  . apply CRhdRhd!_of_C!_C! (K_right hφ) (K_left hψ);
  . apply CRhdRhd!_of_C!_C! (K_left hφ) (K_right hψ);

omit [DecidableEq F] in
@[grind]
lemma ERhdRhd_of_E_E : 𝓢 ⊢ φ₁ ⭤ φ₂ → 𝓢 ⊢ ψ₁ ⭤ ψ₂ → 𝓢 ⊢ (φ₁ ▷ ψ₁) ⭤ (φ₂ ▷ ψ₂) := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ERhdRhd!_of_E!_E! h₁ h₂⟩

-- TODO: Move to entailments
def CC!_of_CC!_of_C! (h₁ : 𝓢 ⊢! φ ➝ ψ ➝ χ) (h₂ : 𝓢 ⊢! χ ➝ ξ) : 𝓢 ⊢! φ ➝ ψ ➝ ξ := by
  apply deduct';
  apply deduct;
  exact (of h₂) ⨀ (deductInv $ deductInv' h₁);
omit [DecidableEq F] in
lemma CC_of_CC_of_C (h₁ : 𝓢 ⊢ φ ➝ ψ ➝ χ) (h₂ : 𝓢 ⊢ χ ➝ ξ) : 𝓢 ⊢ φ ➝ ψ ➝ ξ := ⟨CC!_of_CC!_of_C! h₁.some h₂.some⟩


def CLNRhd! : 𝓢 ⊢! □(∼φ) ➝ (φ ▷ ψ) := by
  apply C_trans CLRhdNO!;
  apply CRhdRhd!_of_C!_C!;
  . apply dni;
  . apply efq;
@[simp, grind] lemma CLNRhd : 𝓢 ⊢ □(∼φ) ➝ (φ ▷ ψ) := ⟨CLNRhd!⟩

def CRhdOLN! : 𝓢 ⊢! φ ▷ ⊥ ➝ □(∼φ) := by
  apply C_trans ?_ CRhdNOL!;
  apply R2!;
  apply dne;
omit [DecidableEq F] in @[simp, grind] lemma CRhdOLN : 𝓢 ⊢ φ ▷ ⊥ ➝ □(∼φ) := ⟨CRhdOLN!⟩

def CLNRhdO! : 𝓢 ⊢! □(∼φ) ➝ (φ ▷ ⊥) := by
  apply C_trans CLRhdNO!;
  apply R2!;
  apply dni;
@[simp, grind] lemma CLNRhdO : 𝓢 ⊢ □(∼φ) ➝ (φ ▷ ⊥) := ⟨CLNRhdO!⟩

-- TODO: Move to entailments
def CCNKN : 𝓢 ⊢! (φ ➝ ψ) ➝ ∼(φ ⋏ ∼ψ) := by
  apply C_replace CCAN CANNNK;
  apply CAA_of_C_right;
  apply dni;

-- TODO: Move to entailments
def CAKN! : 𝓢 ⊢! φ ➝ φ ⋏ ∼ψ ⋎ ψ := by
  apply deduct';
  apply A_replace $ A_symm $ lem (φ := ψ);
  . apply deduct;
    apply K_intro <;> . apply FiniteContext.byAxm; simp;
  . apply C_id;

def CCRhdRhdLC! : 𝓢 ⊢! □(φ ➝ ψ) ➝ (ψ ▷ χ ➝ φ ▷ χ) := by
  suffices 𝓢 ⊢! □(∼(φ ⋏ ∼ψ)) ➝ ψ ▷ χ ➝ φ ▷ χ by apply C_trans (box_regularity CCNKN) this;
  apply C_trans CLNRhd!;
  apply CC!_of_CC!_of_C! J3!;
  apply R2!;
  apply CAKN!;

-- TODO: Move to entailments
def CCC!_of_C!_of_C! (h₁ : 𝓢 ⊢! ψ₁ ➝ φ₁) (h₂ : 𝓢 ⊢! φ₂ ➝ ψ₂) : 𝓢 ⊢! (φ₁ ➝ φ₂) ➝ (ψ₁ ➝ ψ₂) := by
  apply deduct';
  apply C_trans ?_ $ of h₂;
  apply C_trans $ of h₁;
  exact byAxm;

def CCMMCRhdORhdO! : 𝓢 ⊢! (◇φ ➝ ◇ψ) ➝ ψ ▷ ⊥ ➝ φ ▷ ⊥ := by
  suffices 𝓢 ⊢! (□(∼ψ) ➝ □(∼φ)) ➝ ψ ▷ ⊥ ➝ φ ▷ ⊥ by
    apply C_trans ?_ this;
    apply C_trans ?_ CCNNC;
    apply CCC!_of_C!_of_C!;
    . apply INLNM!;
    . apply IMNLN!;
  apply CCC!_of_C!_of_C!;
  . apply CRhdOLN!;
  . apply CLNRhd!;
@[simp] lemma CCMMCRhdORhdO : 𝓢 ⊢ (◇φ ➝ ◇ψ) ➝ (ψ ▷ ⊥ ➝ φ ▷ ⊥) := ⟨CCMMCRhdORhdO!⟩

def CCRhdORhdOCMM! : 𝓢 ⊢! (ψ ▷ ⊥ ➝ φ ▷ ⊥) ➝ (◇φ ➝ ◇ψ) := by
  suffices 𝓢 ⊢! (ψ ▷ ⊥ ➝ φ ▷ ⊥) ➝ (□(∼ψ) ➝ □(∼φ)) by
    apply C_trans this;
    apply C_trans CCCNN;
    apply CCC!_of_C!_of_C!;
    . apply IMNLN!;
    . apply INLNM!;
  apply CCC!_of_C!_of_C!;
  . apply CLNRhd!;
  . apply CRhdOLN!;
@[simp] lemma CCRhdORhdOCMM : 𝓢 ⊢ (ψ ▷ ⊥ ➝ φ ▷ ⊥) ➝ (◇φ ➝ ◇ψ) := ⟨CCRhdORhdOCMM!⟩

end LO.InterpretabilityLogic.Entailment

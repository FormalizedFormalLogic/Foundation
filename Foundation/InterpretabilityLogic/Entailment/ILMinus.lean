module
import Foundation.InterpretabilityLogic.Entailment.Basic
import Foundation.Modal.Entailment.GL


namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [Entailment S F] {𝓢 : S} {φ φ₁ φ₂ φ₃ ψ ψ₁ ψ₂ χ ξ : F}

section

variable [LogicalConnective F] [Entailment.Cl 𝓢]

def CAKK_of_A (h : 𝓢 ⊢! ψ₁ ⋎ ψ₂) : 𝓢 ⊢! φ ➝ φ ⋏ ψ₁ ⋎ φ ⋏ ψ₂ := by
  apply deduct';
  apply A_cases ?_ ?_ (of h);
  . apply deduct;
    apply A_intro_left;
    apply K_intro <;> . apply FiniteContext.byAxm; simp;
  . apply deduct;
    apply A_intro_right;
    apply K_intro <;> . apply FiniteContext.byAxm; simp;

def K_intro₃ (h₁ : 𝓢 ⊢! φ₁) (h₂ : 𝓢 ⊢! φ₂) (h₃ : 𝓢 ⊢! φ₃) : 𝓢 ⊢! φ₁ ⋏ φ₂ ⋏ φ₃ := by
  apply K_intro;
  . assumption;
  . apply K_intro;
    . assumption;
    . assumption;

def K_assoc : 𝓢 ⊢! (φ ⋏ ψ) ⋏ χ ⭤ φ ⋏ (ψ ⋏ χ) := by
  apply K_intro;
  . apply deduct';
    suffices [φ ⋏ ψ, χ] ⊢[𝓢]! φ ⋏ (ψ ⋏ χ) by tauto;
    apply K_intro₃;
    . apply K_left $ FiniteContext.nthAxm 0;
    . apply K_right $ FiniteContext.nthAxm 0;
    . apply FiniteContext.byAxm; simp;
  . apply deduct';
    suffices [φ, ψ, χ] ⊢[𝓢]! (φ ⋏ ψ) ⋏ χ by tauto;
    apply K_intro
    . apply K_intro <;> . apply FiniteContext.byAxm; simp;
    . apply FiniteContext.byAxm; simp;

def K_assoc_mp : 𝓢 ⊢! (φ ⋏ ψ) ⋏ χ ➝ φ ⋏ (ψ ⋏ χ) := K_left K_assoc
def K_assoc_mpr : 𝓢 ⊢! φ ⋏ (ψ ⋏ χ) ➝ (φ ⋏ ψ) ⋏ χ := K_right K_assoc

def AK_of_KA (h : 𝓢 ⊢! (φ ⋏ (ψ ⋎ χ))) : 𝓢 ⊢! (φ ⋏ ψ ⋎ χ) := by
  apply A_cases ?_ ?_ $ K_right h;
  . apply deduct';
    apply A_intro_left;
    apply K_intro;
    . apply of $ K_left h;
    . apply FiniteContext.byAxm; simp;
  . apply deduct';
    apply A_intro_right;
    apply FiniteContext.byAxm; simp;

def CNKCN! : 𝓢 ⊢! ∼(φ ⋏ ψ) ➝ (φ ➝ ∼ψ) := by
  apply C_trans CNKANN;
  apply CA_of_C_of_C;
  . apply CNC;
  . apply implyK;

def ENTO : 𝓢 ⊢! ∼⊤ ⭤ ⊥ := by
  apply E_intro;
  . apply CN_of_CN_left;
    apply C_of_conseq;
    apply verum;
  . exact efq;

def CNTO : 𝓢 ⊢! ∼⊤ ➝ ⊥ := K_left ENTO
def CONT : 𝓢 ⊢! ⊥ ➝ ∼⊤ := K_right ENTO

def CCNNK! : 𝓢 ⊢! (φ ➝ ∼ψ) ➝ ∼(φ ⋏ ψ):= C_replace CCAN CANNNK C_id

def CCNKN : 𝓢 ⊢! (φ ➝ ψ) ➝ ∼(φ ⋏ ∼ψ) := by
  apply C_replace CCAN CANNNK;
  apply CAA_of_C_right;
  apply dni;

def CAKN! : 𝓢 ⊢! φ ➝ φ ⋏ ∼ψ ⋎ ψ := by
  apply deduct';
  apply A_replace $ A_symm $ lem (φ := ψ);
  . apply deduct;
    apply K_intro <;> . apply FiniteContext.byAxm; simp;
  . apply C_id;

def CCC!_of_C!_of_C! (h₁ : 𝓢 ⊢! ψ₁ ➝ φ₁) (h₂ : 𝓢 ⊢! φ₂ ➝ ψ₂) : 𝓢 ⊢! (φ₁ ➝ φ₂) ➝ (ψ₁ ➝ ψ₂) := by
  apply deduct';
  apply C_trans ?_ $ of h₂;
  apply C_trans $ of h₁;
  exact byAxm;

def CCC!_of_C! (h : 𝓢 ⊢! φ₂ ➝ ψ₂) : 𝓢 ⊢! (φ ➝ φ₂) ➝ (φ ➝ ψ₂) := CCC!_of_C!_of_C! C_id h

def CCC!_of_C'! (h : 𝓢 ⊢! ψ₁ ➝ φ₁) : 𝓢 ⊢! (φ₁ ➝ ψ) ➝ (ψ₁ ➝ ψ) := CCC!_of_C!_of_C! h C_id

def replace_CK_left (h₁ : 𝓢 ⊢! φ₂ ➝ φ₁) (h₂ : 𝓢 ⊢! φ₁ ⋏ ψ ➝ χ) : 𝓢 ⊢! φ₂ ⋏ ψ ➝ χ := by
  apply C_trans ?_ h₂;
  apply CKK_of_C h₁;

def replace_CK_right (h₁ : 𝓢 ⊢! ψ₁ ➝ ψ₂) (h₂ : 𝓢 ⊢! φ ⋏ ψ₂ ➝ χ) : 𝓢 ⊢! φ ⋏ ψ₁ ➝ χ := by
  apply C_trans ?_ h₂;
  apply CKK_of_C' h₁;

def left_K_symm (d : 𝓢 ⊢! φ ⋏ ψ ➝ χ) : 𝓢 ⊢! ψ ⋏ φ ➝ χ := C_trans CKK d

def CCNO! : 𝓢 ⊢! φ ➝ ∼φ ➝ ⊥ := C_trans dni (K_left negEquiv)
@[simp] lemma CCNO : 𝓢 ⊢ φ ➝ ∼φ ➝ ⊥ := ⟨CCNO!⟩

def CC!_of_CC!_of_C! (h₁ : 𝓢 ⊢! φ ➝ ψ ➝ χ) (h₂ : 𝓢 ⊢! χ ➝ ξ) : 𝓢 ⊢! φ ➝ ψ ➝ ξ := by
  apply deduct';
  apply deduct;
  exact (of h₂) ⨀ (deductInv $ deductInv' h₁);

omit [DecidableEq F] in
lemma CC_of_CC_of_C (h₁ : 𝓢 ⊢ φ ➝ ψ ➝ χ) (h₂ : 𝓢 ⊢ χ ➝ ξ) : 𝓢 ⊢ φ ➝ ψ ➝ ξ := ⟨CC!_of_CC!_of_C! h₁.some h₂.some⟩


end


section

variable [BasicModalLogicalConnective F] [Modal.Entailment.GL 𝓢]

def CKDiaBoxDiaK! : 𝓢 ⊢! ◇φ ⋏ □ψ ➝ ◇(φ ⋏ ψ) := by
  apply C_of_CNN;
  apply C_replace ?_ ?_ $ axiomK (φ := ψ) (ψ := ∼φ);
  . suffices 𝓢 ⊢! □(∼(φ ⋏ ψ)) ➝ □(ψ ➝ ∼φ) by
      apply C_trans ?_ this;
      apply CN_of_CN_left;
      apply INLNM!;
    apply box_regularity;
    apply C_trans CNKANN;
    apply left_A_intro;
    . apply implyK;
    . apply CNC;
  . apply deduct';
    apply NK_of_ANN;
    apply A_symm;
    apply AN_of_C;
    apply deduct;
    suffices [□ψ, □ψ ➝ □(∼φ)] ⊢[𝓢]! □(∼φ) by
      apply C_trans this;
      apply CN_of_CN_right;
      apply IMNLN!;
    exact (FiniteContext.nthAxm 1) ⨀ (FiniteContext.nthAxm 0)

def CMNNL! : 𝓢 ⊢! ◇(∼φ) ➝ (∼□φ) := by
  apply C_trans IMNLN!;
  apply contra;
  apply box_regularity;
  apply dni;

def CNMLN! : 𝓢 ⊢! ∼◇φ ➝ □(∼φ) := CN_of_CN_left $ INLNM!

def LN!_of_CMN! (h : 𝓢 ⊢! ∼◇φ) : 𝓢 ⊢! □(∼φ) := CNMLN! ⨀ h

def CLNNM! : 𝓢 ⊢! □(∼φ) ➝ ∼◇φ := CN_of_CN_right $ IMNLN!

def NM!_of_LN! (h : 𝓢 ⊢! □(∼φ)) : 𝓢 ⊢! ∼◇φ := CLNNM! ⨀ h

def NMO! : 𝓢 ⊢! ∼◇⊥ := (contra $ K_left diaDuality) ⨀ (dni' $ nec NO)
@[simp] lemma NMO : 𝓢 ⊢ ∼◇⊥ := ⟨NMO!⟩

def diaAxiomL : 𝓢 ⊢! ◇φ ➝ ◇(φ ⋏ □(∼φ)) := by
  apply C_replace IMNLN! INLNM!;
  apply contra;
  apply C_trans ?_ axiomL;
  apply box_regularity;
  apply C_trans CNKCN!;
  apply deduct';
  apply CN_of_CN_right;
  apply FiniteContext.byAxm;
  simp;

end


end LO.InterpretabilityLogic.Entailment



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
@[grind ⇐] lemma CRhdRhd_of_C_C : 𝓢 ⊢ φ₂ ➝ φ₁ → 𝓢 ⊢ ψ₁ ➝ ψ₂ → 𝓢 ⊢ (φ₁ ▷ ψ₁) ➝ (φ₂ ▷ ψ₂) := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨CRhdRhd!_of_C!_C! h₁ h₂⟩


def ERhdRhd!_of_E!_E! (hφ : 𝓢 ⊢! φ₁ ⭤ φ₂) (hψ : 𝓢 ⊢! ψ₁ ⭤ ψ₂) : 𝓢 ⊢! (φ₁ ▷ ψ₁) ⭤ (φ₂ ▷ ψ₂) := by
  apply K_intro;
  . apply CRhdRhd!_of_C!_C! (K_right hφ) (K_left hψ);
  . apply CRhdRhd!_of_C!_C! (K_left hφ) (K_right hψ);

omit [DecidableEq F] in
@[grind ⇐]
lemma ERhdRhd_of_E_E : 𝓢 ⊢ φ₁ ⭤ φ₂ → 𝓢 ⊢ ψ₁ ⭤ ψ₂ → 𝓢 ⊢ (φ₁ ▷ ψ₁) ⭤ (φ₂ ▷ ψ₂) := λ ⟨h₁⟩ ⟨h₂⟩ => ⟨ERhdRhd!_of_E!_E! h₁ h₂⟩


def CLNRhd! : 𝓢 ⊢! □(∼φ) ➝ (φ ▷ ψ) := by
  apply C_trans CLRhdNO!;
  apply CRhdRhd!_of_C!_C!;
  . apply dni;
  . apply efq;
@[simp, grind .] lemma CLNRhd : 𝓢 ⊢ □(∼φ) ➝ (φ ▷ ψ) := ⟨CLNRhd!⟩


def CRhdOLN! : 𝓢 ⊢! φ ▷ ⊥ ➝ □(∼φ) := by
  apply C_trans ?_ CRhdNOL!;
  apply R2!;
  apply dne;
omit [DecidableEq F] in @[simp, grind .] lemma CRhdOLN : 𝓢 ⊢ φ ▷ ⊥ ➝ □(∼φ) := ⟨CRhdOLN!⟩


def CLNRhdO! : 𝓢 ⊢! □(∼φ) ➝ (φ ▷ ⊥) := by
  apply C_trans CLRhdNO!;
  apply R2!;
  apply dni;
@[simp, grind .] lemma CLNRhdO : 𝓢 ⊢ □(∼φ) ➝ (φ ▷ ⊥) := ⟨CLNRhdO!⟩


def CCRhdRhdLC! : 𝓢 ⊢! □(φ ➝ ψ) ➝ (ψ ▷ χ ➝ φ ▷ χ) := by
  suffices 𝓢 ⊢! □(∼(φ ⋏ ∼ψ)) ➝ ψ ▷ χ ➝ φ ▷ χ by apply C_trans (box_regularity CCNKN) this;
  apply C_trans CLNRhd!;
  apply CC!_of_CC!_of_C! axiomJ3!;
  apply R2!;
  apply CAKN!;

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

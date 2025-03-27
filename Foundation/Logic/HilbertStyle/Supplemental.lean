import Foundation.Logic.Entailment
import Foundation.Logic.HilbertStyle.Context

namespace LO.Entailment

variable {F : Type*} [LogicalConnective F] [DecidableEq F]
         {S : Type*} [Entailment F S]
         {𝓢 : S} [Entailment.Minimal 𝓢]
         {φ φ₁ φ₂ ψ ψ₁ ψ₂ χ ξ : F}
         {Γ Δ : List F}

open NegationEquiv
open FiniteContext
open List

def mdp_in : 𝓢 ⊢ φ ⋏ (φ ➝ ψ) ➝ ψ := by
  apply deduct';
  have hp  : [φ, φ ➝ ψ] ⊢[𝓢] φ := FiniteContext.byAxm;
  have hpq : [φ, φ ➝ ψ] ⊢[𝓢] φ ➝ ψ := FiniteContext.byAxm;
  exact hpq ⨀ hp;
lemma mdp_in! : 𝓢 ⊢! φ ⋏ (φ ➝ ψ) ➝ ψ := ⟨mdp_in⟩

def bot_of_mem_either (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢] ⊥ := by
  have hp : Γ ⊢[𝓢] φ := FiniteContext.byAxm h₁;
  have hnp : Γ ⊢[𝓢] φ ➝ ⊥ := cφoOfNφ $ FiniteContext.byAxm h₂;
  exact hnp ⨀ hp

@[simp] lemma bot_of_mem_either! (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢]! ⊥ := ⟨bot_of_mem_either h₁ h₂⟩


def efq_of_mem_either [HasAxiomEFQ 𝓢] (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢] ψ := φOfO $ bot_of_mem_either h₁ h₂
@[simp] lemma efq_of_mem_either! [HasAxiomEFQ 𝓢] (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢]! ψ := ⟨efq_of_mem_either h₁ h₂⟩

def efq_imply_not₁ [HasAxiomEFQ 𝓢] : 𝓢 ⊢ ∼φ ➝ φ ➝ ψ := by
  apply deduct';
  apply deduct;
  apply efq_of_mem_either (φ := φ) (by simp) (by simp);
@[simp] lemma efq_imply_not₁! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! ∼φ ➝ φ ➝ ψ := ⟨efq_imply_not₁⟩

def efq_imply_not₂ [HasAxiomEFQ 𝓢] : 𝓢 ⊢ φ ➝ ∼φ ➝ ψ := by
  apply deduct';
  apply deduct;
  apply efq_of_mem_either (φ := φ) (by simp) (by simp);
@[simp] lemma efq_imply_not₂! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! φ ➝ ∼φ ➝ ψ := ⟨efq_imply_not₂⟩

lemma efq_of_neg! [HasAxiomEFQ 𝓢] (h : 𝓢 ⊢! ∼φ) : 𝓢 ⊢! φ ➝ ψ := by
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  have dnp : [φ] ⊢[𝓢]! φ ➝ ⊥ := of'! $ nφ!_iff_cφo!.mp h;
  exact φ!_of_o! (dnp ⨀ FiniteContext.id!);

lemma efq_of_neg₂! [HasAxiomEFQ 𝓢] (h : 𝓢 ⊢! φ) : 𝓢 ⊢! ∼φ ➝ ψ := efq_imply_not₂! ⨀ h

def neg_mdp (hnp : 𝓢 ⊢ ∼φ) (hn : 𝓢 ⊢ φ) : 𝓢 ⊢ ⊥ := (cφoOfNφ hnp) ⨀ hn
-- infixl:90 "⨀" => neg_mdp

omit [DecidableEq F] in lemma neg_mdp! (hnp : 𝓢 ⊢! ∼φ) (hn : 𝓢 ⊢! φ) : 𝓢 ⊢! ⊥ := ⟨neg_mdp hnp.some hn.some⟩
-- infixl:90 "⨀" => neg_mdp!

def dneOr [HasAxiomDNE 𝓢] (d : 𝓢 ⊢ ∼∼φ ⋎ ∼∼ψ) : 𝓢 ⊢ φ ⋎ ψ := χOfCφχOfCψχOfAφψ (cTrans dne or₁) (cTrans dne or₂) d
omit [DecidableEq F] in lemma dne_or! [HasAxiomDNE 𝓢] (d : 𝓢 ⊢! ∼∼φ ⋎ ∼∼ψ) : 𝓢 ⊢! φ ⋎ ψ := ⟨dneOr d.some⟩

def implyLeftOr' (h : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ φ ➝ (χ ⋎ ψ) := by
  apply deduct';
  apply aφψOfφ;
  apply deductInv;
  exact of h;
omit [DecidableEq F] in lemma imply_left_or'! (h : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! φ ➝ (χ ⋎ ψ) := ⟨implyLeftOr' h.some⟩

def implyRightOr' (h : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ ψ ➝ (φ ⋎ χ) := by
  apply deduct';
  apply aφψOfψ;
  apply deductInv;
  exact of h;
omit [DecidableEq F] in lemma imply_right_or'! (h : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! ψ ➝ (φ ⋎ χ) := ⟨implyRightOr' h.some⟩


def implyRightAnd (hq : 𝓢 ⊢ φ ➝ ψ) (hr : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ φ ➝ ψ ⋏ χ := by
  apply deduct';
  replace hq : [] ⊢[𝓢] φ ➝ ψ := of hq;
  replace hr : [] ⊢[𝓢] φ ➝ χ := of hr;
  exact kφψOfφOfψ (mdp' hq FiniteContext.id) (mdp' hr FiniteContext.id)
lemma imply_right_and! (hq : 𝓢 ⊢! φ ➝ ψ) (hr : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! φ ➝ ψ ⋏ χ := ⟨implyRightAnd hq.some hr.some⟩

omit [DecidableEq F] in lemma imply_left_k!_symm (d : 𝓢 ⊢! φ ⋏ ψ ➝ χ) : 𝓢 ⊢! ψ ⋏ φ ➝ χ := c!_trans ckφψkψφ! d

lemma dhyp_and_left! (h : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! (ψ ⋏ φ) ➝ χ := by
  apply and_imply_iff_imply_imply'!.mpr;
  apply deduct'!;
  exact FiniteContext.of'! (Γ := [ψ]) h;

lemma dhyp_and_right! (h : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! (φ ⋏ ψ) ➝ χ := c!_trans ckφψkψφ! (dhyp_and_left! h)

lemma cut! (d₁ : 𝓢 ⊢! φ₁ ⋏ c ➝ ψ₁) (d₂ : 𝓢 ⊢! φ₂ ➝ c ⋎ ψ₂) : 𝓢 ⊢! φ₁ ⋏ φ₂ ➝ ψ₁ ⋎ ψ₂ := by
  apply deduct'!;
  exact χ!_of_cφχ!_of_cψχ!_of_aφψ! (imply_left_or'! $ of'! (and_imply_iff_imply_imply'!.mp d₁) ⨀ (φ!_of_kφψ! id!)) or₂! (of'! d₂ ⨀ ψ!_of_kφψ! id!);


def orComm : 𝓢 ⊢ φ ⋎ ψ ➝ ψ ⋎ φ := by
  apply deduct';
  exact χOfCφχOfCψχOfAφψ or₂ or₁ $ FiniteContext.id
omit [DecidableEq F] in lemma or_comm! : 𝓢 ⊢! φ ⋎ ψ ➝ ψ ⋎ φ := ⟨orComm⟩

def orComm' (h : 𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ ψ ⋎ φ := orComm ⨀ h
omit [DecidableEq F] in lemma or_comm'! (h : 𝓢 ⊢! φ ⋎ ψ) : 𝓢 ⊢! ψ ⋎ φ := ⟨orComm' h.some⟩

omit [DecidableEq F] in
lemma or_assoc'! : 𝓢 ⊢! φ ⋎ (ψ ⋎ χ) ↔ 𝓢 ⊢! (φ ⋎ ψ) ⋎ χ := by
  constructor;
  . intro h;
    exact χ!_of_cφχ!_of_cψχ!_of_aφψ!
      (imply_left_or'! $ imply_left_or'! c!_id)
      (by
        apply provable_iff_provable.mpr;
        apply deduct_iff.mpr;
        exact χ!_of_cφχ!_of_cψχ!_of_aφψ! (imply_left_or'! $ imply_right_or'! c!_id) (imply_right_or'! c!_id) id!;
      )
      h;
  . intro h;
    exact χ!_of_cφχ!_of_cψχ!_of_aφψ!
      (by
        apply provable_iff_provable.mpr;
        apply deduct_iff.mpr;
        exact χ!_of_cφχ!_of_cψχ!_of_aφψ! (imply_left_or'! c!_id) (imply_right_or'! $ imply_left_or'! c!_id) id!;
      )
      (imply_right_or'! $ imply_right_or'! c!_id)
      h;

omit [DecidableEq F] in
lemma and_assoc! : 𝓢 ⊢! (φ ⋏ ψ) ⋏ χ ⭤ φ ⋏ (ψ ⋏ χ) := by
  apply e!_intro;
  . apply FiniteContext.deduct'!;
    have hp : [(φ ⋏ ψ) ⋏ χ] ⊢[𝓢]! φ := φ!_of_kφψ! $ φ!_of_kφψ! id!;
    have hq : [(φ ⋏ ψ) ⋏ χ] ⊢[𝓢]! ψ := ψ!_of_kφψ! $ φ!_of_kφψ! id!;
    have hr : [(φ ⋏ ψ) ⋏ χ] ⊢[𝓢]! χ := ψ!_of_kφψ! id!;
    exact kφψ!_of_φ!_of_ψ! hp (kφψ!_of_φ!_of_ψ! hq hr);
  . apply FiniteContext.deduct'!;
    have hp : [φ ⋏ (ψ ⋏ χ)] ⊢[𝓢]! φ := φ!_of_kφψ! id!;
    have hq : [φ ⋏ (ψ ⋏ χ)] ⊢[𝓢]! ψ := φ!_of_kφψ! $ ψ!_of_kφψ! id!;
    have hr : [φ ⋏ (ψ ⋏ χ)] ⊢[𝓢]! χ := ψ!_of_kφψ! $ ψ!_of_kφψ! id!;
    apply kφψ!_of_φ!_of_ψ!;
    . exact kφψ!_of_φ!_of_ψ! hp hq;
    . exact hr;

def andReplaceLeft' (hc : 𝓢 ⊢ φ ⋏ ψ) (h : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ χ ⋏ ψ := kφψOfφOfψ (h ⨀ φOfKφψ hc) (ψOfKφψ hc)
omit [DecidableEq F] in lemma and_replace_left'! (hc : 𝓢 ⊢! φ ⋏ ψ) (h : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! χ ⋏ ψ := ⟨andReplaceLeft' hc.some h.some⟩

def andReplaceLeft (h : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ φ ⋏ ψ ➝ χ ⋏ ψ := by
  apply deduct';
  exact andReplaceLeft' FiniteContext.id (of h)
omit [DecidableEq F] in lemma and_replace_left! (h : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! φ ⋏ ψ ➝ χ ⋏ ψ := ⟨andReplaceLeft h.some⟩


def andReplaceRight' (hc : 𝓢 ⊢ φ ⋏ ψ) (h : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ φ ⋏ χ := kφψOfφOfψ (φOfKφψ hc) (h ⨀ ψOfKφψ hc)
omit [DecidableEq F] in lemma andReplaceRight'! (hc : 𝓢 ⊢! φ ⋏ ψ) (h : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! φ ⋏ χ := ⟨andReplaceRight' hc.some h.some⟩

def andReplaceRight (h : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ φ ⋏ ψ ➝ φ ⋏ χ := by
  apply deduct';
  exact andReplaceRight' (FiniteContext.id) (of h)
omit [DecidableEq F] in lemma and_replace_right! (h : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! φ ⋏ ψ ➝ φ ⋏ χ := ⟨andReplaceRight h.some⟩


def andReplace' (hc : 𝓢 ⊢ φ ⋏ ψ) (h₁ : 𝓢 ⊢ φ ➝ χ) (h₂ : 𝓢 ⊢ ψ ➝ ξ) : 𝓢 ⊢ χ ⋏ ξ := andReplaceRight' (andReplaceLeft' hc h₁) h₂
omit [DecidableEq F] in lemma and_replace'! (hc : 𝓢 ⊢! φ ⋏ ψ) (h₁ : 𝓢 ⊢! φ ➝ χ) (h₂ : 𝓢 ⊢! ψ ➝ ξ) : 𝓢 ⊢! χ ⋏ ξ := ⟨andReplace' hc.some h₁.some h₂.some⟩

def andReplace (h₁ : 𝓢 ⊢ φ ➝ χ) (h₂ : 𝓢 ⊢ ψ ➝ ξ) : 𝓢 ⊢ φ ⋏ ψ ➝ χ ⋏ ξ := by
  apply deduct';
  exact andReplace' FiniteContext.id (of h₁) (of h₂)
omit [DecidableEq F] in lemma and_replace! (h₁ : 𝓢 ⊢! φ ➝ χ) (h₂ : 𝓢 ⊢! ψ ➝ ξ) : 𝓢 ⊢! φ ⋏ ψ ➝ χ ⋏ ξ := ⟨andReplace h₁.some h₂.some⟩


def orReplaceLeft' (hc : 𝓢 ⊢ φ ⋎ ψ) (hp : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ χ ⋎ ψ := χOfCφχOfCψχOfAφψ (cTrans hp or₁) (or₂) hc
omit [DecidableEq F] in lemma or_replace_left'! (hc : 𝓢 ⊢! φ ⋎ ψ) (hp : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! χ ⋎ ψ := ⟨orReplaceLeft' hc.some hp.some⟩

def orReplaceLeft (hp : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ φ ⋎ ψ ➝ χ ⋎ ψ := by
  apply deduct';
  exact orReplaceLeft' FiniteContext.id (of hp)
omit [DecidableEq F] in lemma or_replace_left! (hp : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! φ ⋎ ψ ➝ χ ⋎ ψ := ⟨orReplaceLeft hp.some⟩


def orReplaceRight' (hc : 𝓢 ⊢ φ ⋎ ψ) (hq : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ φ ⋎ χ := χOfCφχOfCψχOfAφψ (or₁) (cTrans hq or₂) hc
omit [DecidableEq F] in lemma or_replace_right'! (hc : 𝓢 ⊢! φ ⋎ ψ) (hq : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! φ ⋎ χ := ⟨orReplaceRight' hc.some hq.some⟩

def orReplaceRight (hq : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ φ ⋎ ψ ➝ φ ⋎ χ := by
  apply deduct';
  exact orReplaceRight' FiniteContext.id (of hq)
omit [DecidableEq F] in lemma or_replace_right! (hq : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! φ ⋎ ψ ➝ φ ⋎ χ := ⟨orReplaceRight hq.some⟩


def orReplace' (h : 𝓢 ⊢ φ₁ ⋎ ψ₁) (hp : 𝓢 ⊢ φ₁ ➝ φ₂) (hq : 𝓢 ⊢ ψ₁ ➝ ψ₂) : 𝓢 ⊢ φ₂ ⋎ ψ₂ := orReplaceRight' (orReplaceLeft' h hp) hq

omit [DecidableEq F] in lemma or_replace'! (h : 𝓢 ⊢! φ₁ ⋎ ψ₁) (hp : 𝓢 ⊢! φ₁ ➝ φ₂) (hq : 𝓢 ⊢! ψ₁ ➝ ψ₂) : 𝓢 ⊢! φ₂ ⋎ ψ₂ := ⟨orReplace' h.some hp.some hq.some⟩

def orReplace (hp : 𝓢 ⊢ φ₁ ➝ φ₂) (hq : 𝓢 ⊢ ψ₁ ➝ ψ₂) : 𝓢 ⊢ φ₁ ⋎ ψ₁ ➝ φ₂ ⋎ ψ₂ := by
  apply deduct';
  exact orReplace' FiniteContext.id (of hp) (of hq) ;
omit [DecidableEq F] in lemma or_replace! (hp : 𝓢 ⊢! φ₁ ➝ φ₂) (hq : 𝓢 ⊢! ψ₁ ➝ ψ₂) : 𝓢 ⊢! φ₁ ⋎ ψ₁ ➝ φ₂ ⋎ ψ₂ := ⟨orReplace hp.some hq.some⟩

def orReplaceIff (hp : 𝓢 ⊢ φ₁ ⭤ φ₂) (hq : 𝓢 ⊢ ψ₁ ⭤ ψ₂) : 𝓢 ⊢ φ₁ ⋎ ψ₁ ⭤ φ₂ ⋎ ψ₂ := by
  apply eIntro;
  . exact orReplace (φOfKφψ hp) (φOfKφψ hq);
  . exact orReplace (ψOfKφψ hp) (ψOfKφψ hq);
omit [DecidableEq F] in lemma or_replace_iff! (hp : 𝓢 ⊢! φ₁ ⭤ φ₂) (hq : 𝓢 ⊢! ψ₁ ⭤ ψ₂) : 𝓢 ⊢! φ₁ ⋎ ψ₁ ⭤ φ₂ ⋎ ψ₂ := ⟨orReplaceIff hp.some hq.some⟩

omit [DecidableEq F] in
lemma or_assoc! : 𝓢 ⊢! φ ⋎ (ψ ⋎ χ) ⭤ (φ ⋎ ψ) ⋎ χ := by
  apply e!_intro;
  . exact deduct'! $ or_assoc'!.mp id!;
  . exact deduct'! $ or_assoc'!.mpr id!;

omit [DecidableEq F] in
lemma or_replace_right_iff! (d : 𝓢 ⊢! ψ ⭤ χ) : 𝓢 ⊢! φ ⋎ ψ ⭤ φ ⋎ χ := by
  apply e!_intro;
  . apply or_replace_right!; exact φ!_of_kφψ! d;
  . apply or_replace_right!; exact ψ!_of_kφψ! d;

omit [DecidableEq F] in
lemma or_replace_left_iff! (d : 𝓢 ⊢! φ ⭤ χ) : 𝓢 ⊢! φ ⋎ ψ ⭤ χ ⋎ ψ := by
  apply e!_intro;
  . apply or_replace_left!; exact φ!_of_kφψ! d;
  . apply or_replace_left!; exact ψ!_of_kφψ! d;


def andReplaceIff (hp : 𝓢 ⊢ φ₁ ⭤ φ₂) (hq : 𝓢 ⊢ ψ₁ ⭤ ψ₂) : 𝓢 ⊢ φ₁ ⋏ ψ₁ ⭤ φ₂ ⋏ ψ₂ := by
  apply eIntro;
  . exact andReplace (φOfKφψ hp) (φOfKφψ hq);
  . exact andReplace (ψOfKφψ hp) (ψOfKφψ hq);
omit [DecidableEq F] in lemma and_replace_iff! (hp : 𝓢 ⊢! φ₁ ⭤ φ₂) (hq : 𝓢 ⊢! ψ₁ ⭤ ψ₂) : 𝓢 ⊢! φ₁ ⋏ ψ₁ ⭤ φ₂ ⋏ ψ₂ := ⟨andReplaceIff hp.some hq.some⟩


def impReplaceIff (hp : 𝓢 ⊢ φ₁ ⭤ φ₂) (hq : 𝓢 ⊢ ψ₁ ⭤ ψ₂) : 𝓢 ⊢ (φ₁ ➝ ψ₁) ⭤ (φ₂ ➝ ψ₂) := by
  apply eIntro;
  . apply deduct'; exact cTrans (of $ ψOfKφψ hp) $ cTrans (FiniteContext.id) (of $ φOfKφψ hq);
  . apply deduct'; exact cTrans (of $ φOfKφψ hp) $ cTrans (FiniteContext.id) (of $ ψOfKφψ hq);
omit [DecidableEq F] in lemma imp_replace_iff! (hp : 𝓢 ⊢! φ₁ ⭤ φ₂) (hq : 𝓢 ⊢! ψ₁ ⭤ ψ₂) : 𝓢 ⊢! (φ₁ ➝ ψ₁) ⭤ (φ₂ ➝ ψ₂) := ⟨impReplaceIff hp.some hq.some⟩

omit [DecidableEq F] in
lemma imp_replace_iff!' (hp : 𝓢 ⊢! φ₁ ⭤ φ₂) (hq : 𝓢 ⊢! ψ₁ ⭤ ψ₂) : 𝓢 ⊢! φ₁ ➝ ψ₁ ↔ 𝓢 ⊢! φ₂ ➝ ψ₂ :=
  provable_iff_of_e! (imp_replace_iff! hp hq)

def dni : 𝓢 ⊢ φ ➝ ∼∼φ := by
  apply deduct';
  apply nφOfCφO;
  apply deduct;
  exact bot_of_mem_either (φ := φ) (by simp) (by simp);
@[simp] lemma dni! : 𝓢 ⊢! φ ➝ ∼∼φ := ⟨dni⟩

def dni' (b : 𝓢 ⊢ φ) : 𝓢 ⊢ ∼∼φ := dni ⨀ b
lemma dni'! (b : 𝓢 ⊢! φ) : 𝓢 ⊢! ∼∼φ := ⟨dni' b.some⟩


def dniOr' (d : 𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ ∼∼φ ⋎ ∼∼ψ := χOfCφχOfCψχOfAφψ (cTrans dni or₁) (cTrans dni or₂) d
lemma dni_or'! (d : 𝓢 ⊢! φ ⋎ ψ) : 𝓢 ⊢! ∼∼φ ⋎ ∼∼ψ := ⟨dniOr' d.some⟩

def dniAnd' (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ∼∼φ ⋏ ∼∼ψ := kφψOfφOfψ (dni' $ φOfKφψ d) (dni' $ ψOfKφψ d)
lemma dni_and'! (d : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! ∼∼φ ⋏ ∼∼ψ := ⟨dniAnd' d.some⟩

def falsumDNE : 𝓢 ⊢ ∼∼⊥ ➝ ⊥ := by
  apply deduct'
  have d₁ : [∼∼⊥] ⊢[𝓢] ∼⊥ ➝ ⊥ := cφoOfNφ byAxm₀
  have d₂ : [∼∼⊥] ⊢[𝓢] ∼⊥ := nφOfCφO (cId ⊥)
  exact d₁ ⨀ d₂

def falsumDN : 𝓢 ⊢ ∼∼⊥ ⭤ ⊥ := kIntro falsumDNE dni

def dn [HasAxiomDNE 𝓢] : 𝓢 ⊢ φ ⭤ ∼∼φ := eIntro dni dne
@[simp] lemma dn! [HasAxiomDNE 𝓢] : 𝓢 ⊢! φ ⭤ ∼∼φ := ⟨dn⟩


def contra₀ : 𝓢 ⊢ (φ ➝ ψ) ➝ (∼ψ ➝ ∼φ) := by
  apply deduct';
  apply deduct;
  apply nφOfCφO;
  apply deduct;
  have dp  : [φ, ∼ψ, φ ➝ ψ] ⊢[𝓢] φ := FiniteContext.byAxm;
  have dpq : [φ, ∼ψ, φ ➝ ψ] ⊢[𝓢] φ ➝ ψ := FiniteContext.byAxm;
  have dq  : [φ, ∼ψ, φ ➝ ψ] ⊢[𝓢] ψ := dpq ⨀ dp;
  have dnq : [φ, ∼ψ, φ ➝ ψ] ⊢[𝓢] ψ ➝ ⊥ := cφoOfNφ $ FiniteContext.byAxm;
  exact dnq ⨀ dq;
@[simp] def contra₀! : 𝓢 ⊢! (φ ➝ ψ) ➝ (∼ψ ➝ ∼φ) := ⟨contra₀⟩

def contra₀' (b : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ ∼ψ ➝ ∼φ := contra₀ ⨀ b
lemma contra₀'! (b : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! ∼ψ ➝ ∼φ := ⟨contra₀' b.some⟩

def contra₀x2' (b : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ ∼∼φ ➝ ∼∼ψ := contra₀' $ contra₀' b
lemma contra₀x2'! (b : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! ∼∼φ ➝ ∼∼ψ := ⟨contra₀x2' b.some⟩

def contra₀x2 : 𝓢 ⊢ (φ ➝ ψ) ➝ (∼∼φ ➝ ∼∼ψ) := deduct' $ contra₀x2' FiniteContext.id
@[simp] lemma contra₀x2! : 𝓢 ⊢! (φ ➝ ψ) ➝ (∼∼φ ➝ ∼∼ψ) := ⟨contra₀x2⟩


def contra₁' (b : 𝓢 ⊢ φ ➝ ∼ψ) : 𝓢 ⊢ ψ ➝ ∼φ := cTrans dni (contra₀' b)
lemma contra₁'! (b : 𝓢 ⊢! φ ➝ ∼ψ) : 𝓢 ⊢! ψ ➝ ∼φ := ⟨contra₁' b.some⟩

def contra₁ : 𝓢 ⊢ (φ ➝ ∼ψ) ➝ (ψ ➝ ∼φ) := deduct' $ contra₁' FiniteContext.id
lemma contra₁! : 𝓢 ⊢! (φ ➝ ∼ψ) ➝ (ψ ➝ ∼φ) := ⟨contra₁⟩


def contra₂' [HasAxiomDNE 𝓢] (b : 𝓢 ⊢ ∼φ ➝ ψ) : 𝓢 ⊢ ∼ψ ➝ φ := cTrans (contra₀' b) dne
lemma contra₂'! [HasAxiomDNE 𝓢] (b : 𝓢 ⊢! ∼φ ➝ ψ) : 𝓢 ⊢! ∼ψ ➝ φ := ⟨contra₂' b.some⟩

def contra₂ [HasAxiomDNE 𝓢] : 𝓢 ⊢ (∼φ ➝ ψ) ➝ (∼ψ ➝ φ) := deduct' $ contra₂' FiniteContext.id
@[simp] lemma contra₂! [HasAxiomDNE 𝓢] : 𝓢 ⊢! (∼φ ➝ ψ) ➝ (∼ψ ➝ φ) := ⟨contra₂⟩


def contra₃' [HasAxiomDNE 𝓢] (b : 𝓢 ⊢ ∼φ ➝ ∼ψ) : 𝓢 ⊢ ψ ➝ φ := cTrans dni (contra₂' b)
lemma contra₃'! [HasAxiomDNE 𝓢] (b : 𝓢 ⊢! ∼φ ➝ ∼ψ) : 𝓢 ⊢! ψ ➝ φ := ⟨contra₃' b.some⟩

def contra₃ [HasAxiomDNE 𝓢] : 𝓢 ⊢ (∼φ ➝ ∼ψ) ➝ (ψ ➝ φ) :=  deduct' $ contra₃' FiniteContext.id
@[simp] lemma contra₃! [HasAxiomDNE 𝓢] : 𝓢 ⊢! (∼φ ➝ ∼ψ) ➝ (ψ ➝ φ) := ⟨contra₃⟩


def negReplaceIff' (b : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ ∼φ ⭤ ∼ψ := eIntro (contra₀' $ ψOfKφψ b) (contra₀' $ φOfKφψ b)
lemma neg_replace_iff'! (b : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! ∼φ ⭤ ∼ψ := ⟨negReplaceIff' b.some⟩


def iffNegLeftToRight' [HasAxiomDNE 𝓢] (h : 𝓢 ⊢ φ ⭤ ∼ψ) : 𝓢 ⊢ ∼φ ⭤ ψ := by
  apply eIntro;
  . apply contra₂' $  ψOfKφψ h;
  . apply contra₁' $  φOfKφψ h;
lemma iff_neg_left_to_right'! [HasAxiomDNE 𝓢] (h : 𝓢 ⊢! φ ⭤ ∼ψ) : 𝓢 ⊢! ∼φ ⭤ ψ := ⟨iffNegLeftToRight' h.some⟩

def iffNegRightToLeft' [HasAxiomDNE 𝓢] (h : 𝓢 ⊢ ∼φ ⭤ ψ) : 𝓢 ⊢ φ ⭤ ∼ψ := eSymm $ iffNegLeftToRight' $ eSymm h
lemma iff_neg_right_to_left'! [HasAxiomDNE 𝓢] (h : 𝓢 ⊢! ∼φ ⭤ ψ) : 𝓢 ⊢! φ ⭤ ∼ψ := ⟨iffNegRightToLeft' h.some⟩

section NegationEquiv

variable [Entailment.NegationEquiv 𝓢]

def negnegEquiv : 𝓢 ⊢ ∼∼φ ⭤ ((φ ➝ ⊥) ➝ ⊥) := by
  apply eIntro;
  . exact cTrans (by apply contra₀'; exact ψOfKφψ negEquiv) (φOfKφψ negEquiv)
  . exact cTrans (ψOfKφψ negEquiv) (by apply contra₀'; exact φOfKφψ negEquiv)
@[simp] lemma negneg_equiv! : 𝓢 ⊢! ∼∼φ ⭤ ((φ ➝ ⊥) ➝ ⊥) := ⟨negnegEquiv⟩

def negnegEquiv_dne [HasAxiomDNE 𝓢] : 𝓢 ⊢ φ ⭤ ((φ ➝ ⊥) ➝ ⊥) := eTrans dn negnegEquiv
lemma negnegEquiv_dne! [HasAxiomDNE 𝓢] : 𝓢 ⊢! φ ⭤ ((φ ➝ ⊥) ➝ ⊥) := ⟨negnegEquiv_dne⟩

end NegationEquiv

def elimContra_neg [HasAxiomElimContra 𝓢] : 𝓢 ⊢ ((ψ ➝ ⊥) ➝ (φ ➝ ⊥)) ➝ (φ ➝ ψ) := by
  refine cTrans ?_ elimContra;
  apply deduct';
  exact cTrans (cTrans (φOfKφψ negEquiv) FiniteContext.byAxm) (ψOfKφψ negEquiv);
@[simp] lemma elimContra_neg! [HasAxiomElimContra 𝓢] : 𝓢 ⊢! ((ψ ➝ ⊥) ➝ (φ ➝ ⊥)) ➝ (φ ➝ ψ) := ⟨elimContra_neg⟩


def tne : 𝓢 ⊢ ∼(∼∼φ) ➝ ∼φ := contra₀' dni
@[simp] lemma tne! : 𝓢 ⊢! ∼(∼∼φ) ➝ ∼φ := ⟨tne⟩

def tne' (b : 𝓢 ⊢ ∼(∼∼φ)) : 𝓢 ⊢ ∼φ := tne ⨀ b
lemma tne'! (b : 𝓢 ⊢! ∼(∼∼φ)) : 𝓢 ⊢! ∼φ := ⟨tne' b.some⟩

def tneIff : 𝓢 ⊢ ∼∼∼φ ⭤ ∼φ := kIntro tne dni

def implyLeftReplace (h : 𝓢 ⊢ ψ ➝ φ) : 𝓢 ⊢ (φ ➝ χ) ➝ (ψ ➝ χ) := by
  apply deduct';
  exact cTrans (of h) id;
omit [DecidableEq F] in lemma replace_imply_left! (h : 𝓢 ⊢! ψ ➝ φ) : 𝓢 ⊢! (φ ➝ χ) ➝ (ψ ➝ χ) := ⟨implyLeftReplace h.some⟩

omit [DecidableEq F] in
lemma replace_imply_left_by_iff'! (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! φ ➝ χ ↔ 𝓢 ⊢! ψ ➝ χ := by
  constructor;
  . exact c!_trans $ ψ!_of_kφψ! h;
  . exact c!_trans $ φ!_of_kφψ! h;

omit [DecidableEq F] in
lemma replace_imply_right_by_iff'! (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! χ ➝ φ ↔ 𝓢 ⊢! χ ➝ ψ := by
  constructor;
  . intro hrp; exact c!_trans hrp $ φ!_of_kφψ! h;
  . intro hrq; exact c!_trans hrq $ ψ!_of_kφψ! h;


def impSwap' (h : 𝓢 ⊢ φ ➝ ψ ➝ χ) : 𝓢 ⊢ ψ ➝ φ ➝ χ := by
  apply deduct';
  apply deduct;
  exact (of (Γ := [φ, ψ]) h) ⨀ FiniteContext.byAxm ⨀ FiniteContext.byAxm;
lemma imp_swap'! (h : 𝓢 ⊢! (φ ➝ ψ ➝ χ)) : 𝓢 ⊢! (ψ ➝ φ ➝ χ) := ⟨impSwap' h.some⟩

def impSwap : 𝓢 ⊢ (φ ➝ ψ ➝ χ) ➝ (ψ ➝ φ ➝ χ) := deduct' $ impSwap' FiniteContext.id
@[simp] lemma imp_swap! : 𝓢 ⊢! (φ ➝ ψ ➝ χ) ➝ (ψ ➝ φ ➝ χ) := ⟨impSwap⟩

def ppq (h : 𝓢 ⊢ φ ➝ φ ➝ ψ) : 𝓢 ⊢ φ ➝ ψ := by
  apply deduct';
  have := of (Γ := [φ]) h;
  exact this ⨀ (FiniteContext.byAxm) ⨀ (FiniteContext.byAxm);
lemma ppq! (h : 𝓢 ⊢! φ ➝ φ ➝ ψ) : 𝓢 ⊢! φ ➝ ψ := ⟨ppq h.some⟩

def p_pq_q : 𝓢 ⊢ φ ➝ (φ ➝ ψ) ➝ ψ := impSwap' $ cId _
lemma p_pq_q! : 𝓢 ⊢! φ ➝ (φ ➝ ψ) ➝ ψ := ⟨p_pq_q⟩

def dhyp_imp' (h : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ (χ ➝ φ) ➝ (χ ➝ ψ) := imply₂ ⨀ (cψφOfφ h)
omit [DecidableEq F] in lemma dhyp_imp'! (h : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! (χ ➝ φ) ➝ (χ ➝ ψ) := ⟨dhyp_imp' h.some⟩

def rev_dhyp_imp' (h : 𝓢 ⊢ ψ ➝ φ) : 𝓢 ⊢ (φ ➝ χ) ➝ (ψ ➝ χ) := impSwap' $ cTrans h p_pq_q
lemma rev_dhyp_imp'! (h : 𝓢 ⊢! ψ ➝ φ) : 𝓢 ⊢! (φ ➝ χ) ➝ (ψ ➝ χ) := ⟨rev_dhyp_imp' h.some⟩

-- TODO: Actually this can be computable but it's too slow.
noncomputable def dnDistributeImply : 𝓢 ⊢ ∼∼(φ ➝ ψ) ➝ (∼∼φ ➝ ∼∼ψ) := by
  apply impSwap';
  apply deduct';
  exact cTrans (contra₀x2' $ deductInv $ of $ impSwap' $ contra₀x2) tne;
@[simp] lemma dn_distribute_imply! : 𝓢 ⊢! ∼∼(φ ➝ ψ) ➝ (∼∼φ ➝ ∼∼ψ) := ⟨dnDistributeImply⟩

noncomputable def dnDistributeImply' (b : 𝓢 ⊢ ∼∼(φ ➝ ψ)) : 𝓢 ⊢ ∼∼φ ➝ ∼∼ψ := dnDistributeImply ⨀ b
lemma dn_distribute_imply'! (b : 𝓢 ⊢! ∼∼(φ ➝ ψ)) : 𝓢 ⊢! ∼∼φ ➝ ∼∼ψ := ⟨dnDistributeImply' b.some⟩


def introFalsumOfAnd' (h : 𝓢 ⊢ φ ⋏ ∼φ) : 𝓢 ⊢ ⊥ := (cφoOfNφ $ ψOfKφψ h) ⨀ (φOfKφψ h)
omit [DecidableEq F] in lemma intro_falsum_of_and'! (h : 𝓢 ⊢! φ ⋏ ∼φ) : 𝓢 ⊢! ⊥ := ⟨introFalsumOfAnd' h.some⟩
/-- Law of contradiction -/
alias lac'! := intro_falsum_of_and'!

def introFalsumOfAnd : 𝓢 ⊢ φ ⋏ ∼φ ➝ ⊥ := by
  apply deduct';
  exact introFalsumOfAnd' (φ := φ) $ FiniteContext.id
omit [DecidableEq F] in @[simp] lemma intro_bot_of_and! : 𝓢 ⊢! φ ⋏ ∼φ ➝ ⊥ := ⟨introFalsumOfAnd⟩
/-- Law of contradiction -/
alias lac! := intro_bot_of_and!



def implyOfNotOr [HasAxiomEFQ 𝓢] : 𝓢 ⊢ (∼φ ⋎ ψ) ➝ (φ ➝ ψ) := cAφψχOfCφχOfCψχ (by
    apply emptyPrf;
    apply deduct;
    apply deduct;
    exact efq_of_mem_either (φ := φ) (by simp) (by simp)
  ) imply₁
@[simp] lemma imply_of_not_or! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! (∼φ ⋎ ψ) ➝ (φ ➝ ψ) := ⟨implyOfNotOr⟩

def implyOfNotOr' [HasAxiomEFQ 𝓢] (b : 𝓢 ⊢ ∼φ ⋎ ψ) : 𝓢 ⊢ φ ➝ ψ := implyOfNotOr ⨀ b
lemma imply_of_not_or'! [HasAxiomEFQ 𝓢] (b : 𝓢 ⊢! ∼φ ⋎ ψ) : 𝓢 ⊢! φ ➝ ψ := ⟨implyOfNotOr' b.some⟩


def demorgan₁ : 𝓢 ⊢ (∼φ ⋎ ∼ψ) ➝ ∼(φ ⋏ ψ) := cAφψχOfCφχOfCψχ (contra₀' and₁) (contra₀' and₂)
@[simp] lemma demorgan₁! : 𝓢 ⊢! (∼φ ⋎ ∼ψ) ➝ ∼(φ ⋏ ψ) := ⟨demorgan₁⟩

def demorgan₁' (d : 𝓢 ⊢ ∼φ ⋎ ∼ψ) : 𝓢 ⊢ ∼(φ ⋏ ψ)  := demorgan₁ ⨀ d
lemma demorgan₁'! (d : 𝓢 ⊢! ∼φ ⋎ ∼ψ) : 𝓢 ⊢! ∼(φ ⋏ ψ) := ⟨demorgan₁' d.some⟩


def demorgan₂ : 𝓢 ⊢ (∼φ ⋏ ∼ψ) ➝ ∼(φ ⋎ ψ) := by
  apply ckφψχOfCφcψχ;
  apply deduct';
  apply deduct;
  apply nφOfCφO;
  apply deduct;
  exact χOfCφχOfCψχOfAφψ (cφoOfNφ FiniteContext.byAxm) (cφoOfNφ FiniteContext.byAxm) (FiniteContext.byAxm (φ := φ ⋎ ψ));
@[simp] lemma demorgan₂! : 𝓢 ⊢! ∼φ ⋏ ∼ψ ➝ ∼(φ ⋎ ψ) := ⟨demorgan₂⟩

def demorgan₂' (d : 𝓢 ⊢ ∼φ ⋏ ∼ψ) : 𝓢 ⊢ ∼(φ ⋎ ψ) := demorgan₂ ⨀ d
lemma demorgan₂'! (d : 𝓢 ⊢! ∼φ ⋏ ∼ψ) : 𝓢 ⊢! ∼(φ ⋎ ψ) := ⟨demorgan₂' d.some⟩


def demorgan₃ : 𝓢 ⊢ ∼(φ ⋎ ψ) ➝ (∼φ ⋏ ∼ψ) := by
  apply deduct';
  exact kφψOfφOfψ (deductInv $ contra₀' $ or₁) (deductInv $ contra₀' $ or₂)
@[simp] lemma demorgan₃! : 𝓢 ⊢! ∼(φ ⋎ ψ) ➝ (∼φ ⋏ ∼ψ) := ⟨demorgan₃⟩

def demorgan₃' (b : 𝓢 ⊢ ∼(φ ⋎ ψ)) : 𝓢 ⊢ ∼φ ⋏ ∼ψ := demorgan₃ ⨀ b
lemma demorgan₃'! (b : 𝓢 ⊢! ∼(φ ⋎ ψ)) : 𝓢 ⊢! ∼φ ⋏ ∼ψ := ⟨demorgan₃' b.some⟩


-- TODO: Actually this can be computable but it's too slow.
noncomputable def demorgan₄ [HasAxiomDNE 𝓢] : 𝓢 ⊢ ∼(φ ⋏ ψ) ➝ (∼φ ⋎ ∼ψ) := by
  apply contra₂';
  apply deduct';
  exact andReplace' (demorgan₃' $ FiniteContext.id) dne dne;
@[simp] lemma demorgan₄! [HasAxiomDNE 𝓢] : 𝓢 ⊢! ∼(φ ⋏ ψ) ➝ (∼φ ⋎ ∼ψ) := ⟨demorgan₄⟩

noncomputable def demorgan₄' [HasAxiomDNE 𝓢] (b : 𝓢 ⊢ ∼(φ ⋏ ψ)) : 𝓢 ⊢ ∼φ ⋎ ∼ψ := demorgan₄ ⨀ b
lemma demorgan₄'! [HasAxiomDNE 𝓢] (b : 𝓢 ⊢! ∼(φ ⋏ ψ)) : 𝓢 ⊢! ∼φ ⋎ ∼ψ := ⟨demorgan₄' b.some⟩

-- TODO: Actually this can be computable but it's too slow.
noncomputable def NotOrOfImply' [HasAxiomDNE 𝓢] (d : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ ∼φ ⋎ ψ := by
  apply φOfNnφ;
  apply nφOfCφO;
  apply deduct';
  have d₁ : [∼(∼φ ⋎ ψ)] ⊢[𝓢] ∼∼φ ⋏ ∼ψ := demorgan₃' $ FiniteContext.id;
  have d₂ : [∼(∼φ ⋎ ψ)] ⊢[𝓢] ∼φ ➝ ⊥ := cφoOfNφ $ φOfKφψ d₁;
  have d₃ : [∼(∼φ ⋎ ψ)] ⊢[𝓢] ∼φ := (of (Γ := [∼(∼φ ⋎ ψ)]) $ contra₀' d) ⨀ (ψOfKφψ d₁);
  exact d₂ ⨀ d₃;
lemma not_or_of_imply'! [HasAxiomDNE 𝓢] (d : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! ∼φ ⋎ ψ := ⟨NotOrOfImply' d.some⟩

noncomputable def NotOrOfImply [HasAxiomDNE 𝓢]  : 𝓢 ⊢ (φ ➝ ψ) ➝ (∼φ ⋎ ψ) := by
  apply deduct';
  apply NotOrOfImply';
  exact FiniteContext.byAxm;
lemma not_or_of_imply! [HasAxiomDNE 𝓢] : 𝓢 ⊢! (φ ➝ ψ) ➝ ∼φ ⋎ ψ := ⟨NotOrOfImply⟩

-- TODO: Actually this can be computable but it's too slow.
noncomputable def dnCollectImply [HasAxiomEFQ 𝓢] : 𝓢 ⊢ (∼∼φ ➝ ∼∼ψ) ➝ ∼∼(φ ➝ ψ) := by
  apply deduct';
  apply nφOfCφO;
  exact cTrans
    (by
      apply deductInv;
      apply cφcψχOfCkφψχ;
      apply deduct;
      have d₁ : [(∼∼φ ➝ ∼∼ψ) ⋏ ∼(φ ➝ ψ)] ⊢[𝓢] ∼∼φ ➝ ∼∼ψ := φOfKφψ (ψ := ∼(φ ➝ ψ)) $ FiniteContext.id;
      have d₂ : [(∼∼φ ➝ ∼∼ψ) ⋏ ∼(φ ➝ ψ)] ⊢[𝓢] ∼∼φ ⋏ ∼ψ := demorgan₃' $ (contra₀' implyOfNotOr) ⨀ (ψOfKφψ (φ := (∼∼φ ➝ ∼∼ψ)) $ FiniteContext.id)
      exact kφψOfφOfψ (ψOfKφψ d₂) (d₁ ⨀ (φOfKφψ d₂))
    )
    (introFalsumOfAnd (φ := ∼ψ));

@[simp] lemma dn_collect_imply! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! (∼∼φ ➝ ∼∼ψ) ➝ ∼∼(φ ➝ ψ) := ⟨dnCollectImply⟩

-- TODO: Actually this can be computable but it's too slow.
noncomputable def dnCollectImply' [HasAxiomEFQ 𝓢] (b : 𝓢 ⊢ ∼∼φ ➝ ∼∼ψ) : 𝓢 ⊢ ∼∼(φ ➝ ψ) := dnCollectImply ⨀ b
lemma dn_collect_imply'! [HasAxiomEFQ 𝓢] (b : 𝓢 ⊢! ∼∼φ ➝ ∼∼ψ) : 𝓢 ⊢! ∼∼(φ ➝ ψ) := ⟨dnCollectImply' b.some⟩


def andImplyAndOfImply {φ ψ φ' ψ' : F} (bp : 𝓢 ⊢ φ ➝ φ') (bq : 𝓢 ⊢ ψ ➝ ψ') : 𝓢 ⊢ φ ⋏ ψ ➝ φ' ⋏ ψ' :=
  deduct' <| kIntro
    (deductInv' <| cTrans and₁ bp)
    (deductInv' <| cTrans and₂ bq)

def andIffAndOfIff {φ ψ φ' ψ' : F} (bp : 𝓢 ⊢ φ ⭤ φ') (bq : 𝓢 ⊢ ψ ⭤ ψ') : 𝓢 ⊢ φ ⋏ ψ ⭤ φ' ⋏ ψ' :=
  eIntro (andImplyAndOfImply (andLeft bp) (andLeft bq)) (andImplyAndOfImply (andRight bp) (andRight bq))


section

instance [HasAxiomEFQ 𝓢] [HasAxiomLEM 𝓢] : HasAxiomDNE 𝓢 where
  dne φ := by
    apply deduct';
    exact χOfCφχOfCψχOfAφψ (cId _) (by
      apply deduct;
      have nnp : [∼φ, ∼∼φ] ⊢[𝓢] ∼φ ➝ ⊥ := cφoOfNφ $ FiniteContext.byAxm;
      have np : [∼φ, ∼∼φ] ⊢[𝓢] ∼φ := FiniteContext.byAxm;
      exact φOfO $ nnp ⨀ np;
    ) $ of lem;;

end


section

-- TODO: Actually this can be computable but it's too slow.
noncomputable instance [HasAxiomDNE 𝓢] : HasAxiomLEM 𝓢 where
  lem _ := dneOr $ NotOrOfImply' dni

instance [HasAxiomDNE 𝓢] : HasAxiomEFQ 𝓢 where
  efq φ := by
    apply contra₃';
    exact cTrans (φOfKφψ negEquiv) $ cTrans (impSwap' imply₁) (ψOfKφψ negEquiv);

instance [HasAxiomDNE 𝓢] : HasAxiomElimContra 𝓢 where
  elimContra φ ψ := by
    apply deduct';
    have : [∼ψ ➝ ∼φ] ⊢[𝓢] ∼ψ ➝ ∼φ := FiniteContext.byAxm;
    exact contra₃' this;

end


noncomputable def implyIffNotOr [HasAxiomDNE 𝓢] : 𝓢 ⊢ (φ ➝ ψ) ⭤ (∼φ ⋎ ψ) := eIntro
  NotOrOfImply (deduct' (orCases efq_imply_not₁ imply₁ byAxm₀))

noncomputable def imply_iff_not_or! [HasAxiomDNE 𝓢] : 𝓢 ⊢! (φ ➝ ψ) ⭤ (∼φ ⋎ ψ) := ⟨implyIffNotOr⟩

def conjIffConj : (Γ : List F) → 𝓢 ⊢ ⋀Γ ⭤ Γ.conj
  | []          => eId ⊤
  | [_]         => eIntro (deduct' <| kIntro FiniteContext.id verum) and₁
  | φ :: ψ :: Γ => andIffAndOfIff (eId φ) (conjIffConj (ψ :: Γ))
omit [DecidableEq F] in @[simp] lemma conjIffConj! : 𝓢 ⊢! ⋀Γ ⭤ Γ.conj := ⟨conjIffConj Γ⟩


omit [DecidableEq F] in lemma implyLeft_conj_eq_conj! : 𝓢 ⊢! Γ.conj ➝ φ ↔ 𝓢 ⊢! ⋀Γ ➝ φ := replace_imply_left_by_iff'! $ e!_symm conjIffConj!


lemma generalConj'! (h : φ ∈ Γ) : 𝓢 ⊢! ⋀Γ ➝ φ := replace_imply_left_by_iff'! conjIffConj! |>.mpr (general_conj! h)
lemma generalConj'₂! (h : φ ∈ Γ) (d : 𝓢 ⊢! ⋀Γ) : 𝓢 ⊢! φ := (generalConj'! h) ⨀ d

section Conjunction

omit [DecidableEq F] in
lemma imply_finset_conj! (φ : F) (s : Finset F) (b : (ψ : F) → ψ ∈ s → 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! φ ➝ s.conj :=
  imply_conj! φ s.toList fun ψ hψ ↦ b ψ (by simpa using hψ)

lemma general_finset_conj! {s : Finset F} (h : φ ∈ s) : 𝓢 ⊢! s.conj ➝ φ := general_conj! <| by simp [h]

omit [DecidableEq F] in
lemma imply_finset_iConj! [Fintype ι] (φ : F) (ψ : ι → F) (b : (i : ι) → 𝓢 ⊢! φ ➝ ψ i) :
    𝓢 ⊢! φ ➝ ⩕ i, ψ i := imply_finset_conj! φ _ (by simpa using b)

lemma general_finset_iConj! [Fintype ι] (φ : ι → F) (i) : 𝓢 ⊢! (⩕ i, φ i) ➝ φ i := general_finset_conj! <| by simp

omit [DecidableEq F] in
lemma iff_provable_list_conj {Γ : List F} : (𝓢 ⊢! ⋀Γ) ↔ (∀ φ ∈ Γ, 𝓢 ⊢! φ) := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp;
  | hcons φ Γ hΓ ih =>
    simp_all;
    constructor;
    . intro h;
      constructor;
      . exact φ!_of_kφψ! h;
      . exact ih.mp (ψ!_of_kφψ! h);
    . rintro ⟨h₁, h₂⟩;
      exact kφψ!_of_φ!_of_ψ! h₁ (ih.mpr h₂);

lemma conjconj_subset! (h : ∀ φ, φ ∈ Γ → φ ∈ Δ) : 𝓢 ⊢! ⋀Δ ➝ ⋀Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp_all; exact generalConj'! h;
  | hcons φ Γ hne ih => simp_all; exact imply_right_and! (generalConj'! h.1) ih;

lemma conjconj_provable! (h : ∀ φ, φ ∈ Γ → Δ ⊢[𝓢]! φ) : 𝓢 ⊢! ⋀Δ ➝ ⋀Γ :=
  by induction Γ using List.induction_with_singleton with
  | hnil => exact cψφ!_of_φ! verum!;
  | hsingle => simp_all; exact provable_iff.mp h;
  | hcons φ Γ hne ih => simp_all; exact imply_right_and! (provable_iff.mp h.1) ih;

lemma conjconj_provable₂! (h : ∀ φ, φ ∈ Γ → Δ ⊢[𝓢]! φ) : Δ ⊢[𝓢]! ⋀Γ := provable_iff.mpr $ conjconj_provable! h

lemma id_conj! (he : ∀ g ∈ Γ, g = φ) : 𝓢 ⊢! φ ➝ ⋀Γ := by
  induction Γ using List.induction_with_singleton with
  | hcons χ Γ h ih =>
    simp_all;
    have ⟨he₁, he₂⟩ := he; subst he₁;
    exact imply_right_and! c!_id ih;
  | _ => simp_all;

lemma replace_imply_left_conj! (he : ∀ g ∈ Γ, g = φ) (hd : 𝓢 ⊢! ⋀Γ ➝ ψ) : 𝓢 ⊢! φ ➝ ψ := c!_trans (id_conj! he) hd

lemma iff_imply_left_cons_conj'! : 𝓢 ⊢! ⋀(φ :: Γ) ➝ ψ ↔ 𝓢 ⊢! φ ⋏ ⋀Γ ➝ ψ := by
  induction Γ with
  | nil =>
    simp [and_imply_iff_imply_imply'!];
    constructor;
    . intro h; apply imp_swap'!; exact cψφ!_of_φ! h;
    . intro h; exact imp_swap'! h ⨀ verum!;
  | cons ψ ih => simp;

omit [DecidableEq F] in
@[simp] lemma imply_left_concat_conj! : 𝓢 ⊢! ⋀(Γ ++ Δ) ➝ ⋀Γ ⋏ ⋀Δ := by
  apply FiniteContext.deduct'!;
  have : [⋀(Γ ++ Δ)] ⊢[𝓢]! ⋀(Γ ++ Δ) := id!;
  have d := iff_provable_list_conj.mp this;
  apply kφψ!_of_φ!_of_ψ!;
  . apply iff_provable_list_conj.mpr;
    intro φ hp;
    exact d φ (by simp; left; exact hp);
  . apply iff_provable_list_conj.mpr;
    intro φ hp;
    exact d φ (by simp; right; exact hp);

@[simp]
lemma forthback_conj_remove! : 𝓢 ⊢! ⋀(Γ.remove φ) ⋏ φ ➝ ⋀Γ := by
  apply deduct'!;
  apply iff_provable_list_conj.mpr;
  intro ψ hq;
  by_cases e : ψ = φ;
  . subst e; exact ψ!_of_kφψ! id!;
  . exact iff_provable_list_conj.mp (φ!_of_kφψ! id!) ψ (by apply List.mem_remove_iff.mpr; simp_all);

lemma imply_left_remove_conj! (b : 𝓢 ⊢! ⋀Γ ➝ ψ) : 𝓢 ⊢! ⋀(Γ.remove φ) ⋏ φ ➝ ψ := c!_trans forthback_conj_remove! b

omit [DecidableEq F] in
lemma iff_concat_conj'! : 𝓢 ⊢! ⋀(Γ ++ Δ) ↔ 𝓢 ⊢! ⋀Γ ⋏ ⋀Δ := by
  constructor;
  . intro h;
    replace h := iff_provable_list_conj.mp h;
    apply kφψ!_of_φ!_of_ψ!;
    . apply iff_provable_list_conj.mpr;
      intro φ hp; exact h φ (by simp only [List.mem_append]; left; simpa);
    . apply iff_provable_list_conj.mpr;
      intro φ hp; exact h φ (by simp only [List.mem_append]; right; simpa);
  . intro h;
    apply iff_provable_list_conj.mpr;
    simp only [List.mem_append];
    rintro φ (hp₁ | hp₂);
    . exact (iff_provable_list_conj.mp $ φ!_of_kφψ! h) φ hp₁;
    . exact (iff_provable_list_conj.mp $ ψ!_of_kφψ! h) φ hp₂;

omit [DecidableEq F] in
@[simp] lemma iff_concat_conj! : 𝓢 ⊢! ⋀(Γ ++ Δ) ⭤ ⋀Γ ⋏ ⋀Δ := by
  apply e!_intro;
  . apply deduct'!; apply iff_concat_conj'!.mp; exact id!;
  . apply deduct'!; apply iff_concat_conj'!.mpr; exact id!;

omit [DecidableEq F] in
lemma imply_left_conj_concat! : 𝓢 ⊢! ⋀(Γ ++ Δ) ➝ φ ↔ 𝓢 ⊢! (⋀Γ ⋏ ⋀Δ) ➝ φ := by
  constructor;
  . intro h; exact c!_trans (ψ!_of_kφψ! iff_concat_conj!) h;
  . intro h; exact c!_trans (φ!_of_kφψ! iff_concat_conj!) h;

end Conjunction

section disjunction

def implyDisj (Γ : List F) (h : φ ∈ Γ) : 𝓢 ⊢ φ ➝ Γ.disj :=
  match Γ with
  |     [] => by simp at h
  | ψ :: Γ =>
    if e : φ = ψ then cast (by simp [e]) (or₁ : 𝓢 ⊢ φ ➝ φ ⋎ Γ.disj)
    else
      have : φ ∈ Γ := by simpa [e] using h
      cTrans (implyDisj Γ this) or₂
def imply_disj! (Γ : List F) (h : φ ∈ Γ) : 𝓢 ⊢! φ ➝ Γ.disj := ⟨implyDisj Γ h⟩

def disjImply [HasAxiomEFQ 𝓢] (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢ ψ ➝ φ) : 𝓢 ⊢ Γ.disj ➝ φ :=
  match Γ with
  |     [] => efq
  | ψ :: Γ => cAφψχOfCφχOfCψχ (b ψ (by simp)) <| disjImply Γ fun ψ h ↦ b ψ (by simp [h])
def disj_imply! [HasAxiomEFQ 𝓢] (Γ : List F) (b : (ψ : F) → ψ ∈ Γ → 𝓢 ⊢! ψ ➝ φ) : 𝓢 ⊢! Γ.disj ➝ φ :=
  ⟨disjImply Γ fun ψ h ↦ (b ψ h).get⟩

lemma imply_finset_disj (s : Finset F) (h : φ ∈ s) : 𝓢 ⊢! φ ➝ s.disj := imply_disj! _ (by simp [h])

omit [DecidableEq F] in
lemma finset_disj_imply! [HasAxiomEFQ 𝓢] (s : Finset F) (b : (ψ : F) → ψ ∈ s → 𝓢 ⊢! ψ ➝ φ) : 𝓢 ⊢! s.disj ➝ φ :=
  disj_imply! _ fun ψ h ↦ b ψ (by simpa using h)

lemma imply_iDisj [Fintype ι] (φ : ι → F) : 𝓢 ⊢! φ i ➝ ⩖ j, φ j := imply_finset_disj _ (by simp)

omit [DecidableEq F] in
lemma iDisj_imply! [HasAxiomEFQ 𝓢] [Fintype ι] (ψ : ι → F) (b : (i : ι) → 𝓢 ⊢! ψ i ➝ φ) : 𝓢 ⊢! (⩖ i, ψ i) ➝ φ :=
  finset_disj_imply! _ (by simpa)

omit [DecidableEq F] in
lemma iff_concact_disj! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! ⋁(Γ ++ Δ) ⭤ ⋁Γ ⋎ ⋁Δ := by
  induction Γ using List.induction_with_singleton generalizing Δ <;> induction Δ using List.induction_with_singleton;
  case hnil.hnil =>
    simp_all;
    apply e!_intro;
    . simp;
    . exact caφψχ!_of_cφχ!_of_cψχ! efq! efq!;
  case hnil.hsingle =>
    simp_all;
    apply e!_intro;
    . simp;
    . exact caφψχ!_of_cφχ!_of_cψχ! efq! c!_id;
  case hsingle.hnil =>
    simp_all;
    apply e!_intro;
    . simp;
    . exact caφψχ!_of_cφχ!_of_cψχ! c!_id efq!;
  case hcons.hnil =>
    simp_all;
    apply e!_intro;
    . simp;
    . exact caφψχ!_of_cφχ!_of_cψχ! c!_id efq!;
  case hnil.hcons =>
    simp_all;
    apply e!_intro;
    . simp;
    . exact caφψχ!_of_cφχ!_of_cψχ! efq! c!_id;
  case hsingle.hsingle => simp_all;
  case hsingle.hcons => simp_all;
  case hcons.hsingle φ ps hps ihp ψ =>
    simp_all;
    apply e!_trans (by
      apply or_replace_right_iff!;
      simpa using @ihp [ψ];
    ) or_assoc!;
  case hcons.hcons φ ps hps ihp ψ qs hqs ihq =>
    simp_all;
    exact e!_trans (by
      apply or_replace_right_iff!;
      exact e!_trans (@ihp (ψ :: qs)) (by
        apply or_replace_right_iff!;
        simp_all;
      )
    ) or_assoc!;

omit [DecidableEq F] in
lemma iff_concact_disj'! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! ⋁(Γ ++ Δ) ↔ 𝓢 ⊢! ⋁Γ ⋎ ⋁Δ := by
  constructor;
  . intro h; exact (φ!_of_kφψ! iff_concact_disj!) ⨀ h;
  . intro h; exact (ψ!_of_kφψ! iff_concact_disj!) ⨀ h;

omit [DecidableEq F] in
lemma implyRight_cons_disj! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! φ ➝ ⋁(ψ :: Γ) ↔ 𝓢 ⊢! φ ➝ ψ ⋎ ⋁Γ := by
  induction Γ with
  | nil =>
    simp;
    constructor;
    . intro h; exact c!_trans h or₁!;
    . intro h; exact c!_trans h $ caφψχ!_of_cφχ!_of_cψχ! c!_id efq!;
  | cons ψ ih => simp;

@[simp]
lemma forthback_disj_remove [HasAxiomEFQ 𝓢] : 𝓢 ⊢! ⋁Γ ➝ φ ⋎ ⋁(Γ.remove φ) := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle ψ =>
    simp;
    by_cases h: ψ = φ;
    . subst_vars; simp;
    . simp [(List.remove_singleton_of_ne h)];
  | hcons ψ Γ h ih =>
    simp_all;
    by_cases hpq : ψ = φ;
    . simp_all only [ne_eq, List.remove_cons_self]; exact caφψχ!_of_cφχ!_of_cψχ! or₁! ih;
    . simp_all [(List.remove_cons_of_ne Γ hpq)];
      by_cases hqΓ : Γ.remove φ = [];
      . simp_all;
        exact caφψχ!_of_cφχ!_of_cψχ! or₂! (c!_trans ih $ or_replace_right! efq!);
      . simp_all;
        exact caφψχ!_of_cφχ!_of_cψχ! (c!_trans or₁! or₂!) (c!_trans ih (or_replace_right! or₂!));

lemma disj_allsame! [HasAxiomEFQ 𝓢] (hd : ∀ ψ ∈ Γ, ψ = φ) : 𝓢 ⊢! ⋁Γ ➝ φ := by
  induction Γ using List.induction_with_singleton with
  | hcons ψ Δ hΔ ih =>
    simp_all;
    have ⟨hd₁, hd₂⟩ := hd; subst hd₁;
    apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    exact χ!_of_cφχ!_of_cψχ!_of_aφψ! (by simp) (weakening! (by simp) $ provable_iff_provable.mp $ ih) id!
  | _ => simp_all;

lemma disj_allsame'! [HasAxiomEFQ 𝓢] (hd : ∀ ψ ∈ Γ, ψ = φ) (h : 𝓢 ⊢! ⋁Γ) : 𝓢 ⊢! φ := (disj_allsame! hd) ⨀ h

end disjunction

section consistency

variable [HasAxiomEFQ 𝓢]

omit [DecidableEq F] in
lemma inconsistent_of_provable_of_unprovable {φ : F}
    (hp : 𝓢 ⊢! φ) (hn : 𝓢 ⊢! ∼φ) : Inconsistent 𝓢 := by
  have : 𝓢 ⊢! φ ➝ ⊥ := nφ!_iff_cφo!.mp hn
  intro ψ; exact efq! ⨀ (this ⨀ hp)

end consistency

end LO.Entailment

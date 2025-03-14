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
  have hnp : Γ ⊢[𝓢] φ ➝ ⊥ := neg_equiv'.mp $ FiniteContext.byAxm h₂;
  exact hnp ⨀ hp

@[simp] lemma bot_of_mem_either! (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢]! ⊥ := ⟨bot_of_mem_either h₁ h₂⟩


def efq_of_mem_either [HasAxiomEFQ 𝓢] (h₁ : φ ∈ Γ) (h₂ : ∼φ ∈ Γ) : Γ ⊢[𝓢] ψ := efq' $ bot_of_mem_either h₁ h₂
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
  have dnp : [φ] ⊢[𝓢]! φ ➝ ⊥ := of'! $ neg_equiv'!.mp h;
  exact efq'! (dnp ⨀ FiniteContext.id!);

lemma efq_of_neg₂! [HasAxiomEFQ 𝓢] (h : 𝓢 ⊢! φ) : 𝓢 ⊢! ∼φ ➝ ψ := efq_imply_not₂! ⨀ h

def neg_mdp (hnp : 𝓢 ⊢ ∼φ) (hn : 𝓢 ⊢ φ) : 𝓢 ⊢ ⊥ := (neg_equiv'.mp hnp) ⨀ hn
-- infixl:90 "⨀" => neg_mdp

omit [DecidableEq F] in lemma neg_mdp! (hnp : 𝓢 ⊢! ∼φ) (hn : 𝓢 ⊢! φ) : 𝓢 ⊢! ⊥ := ⟨neg_mdp hnp.some hn.some⟩
-- infixl:90 "⨀" => neg_mdp!

def dneOr [HasAxiomDNE 𝓢] (d : 𝓢 ⊢ ∼∼φ ⋎ ∼∼ψ) : 𝓢 ⊢ φ ⋎ ψ := or₃''' (impTrans'' dne or₁) (impTrans'' dne or₂) d
omit [DecidableEq F] in lemma dne_or! [HasAxiomDNE 𝓢] (d : 𝓢 ⊢! ∼∼φ ⋎ ∼∼ψ) : 𝓢 ⊢! φ ⋎ ψ := ⟨dneOr d.some⟩

def implyLeftOr' (h : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ φ ➝ (χ ⋎ ψ) := by
  apply deduct';
  apply or₁';
  apply deductInv;
  exact of h;
omit [DecidableEq F] in lemma imply_left_or'! (h : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! φ ➝ (χ ⋎ ψ) := ⟨implyLeftOr' h.some⟩

def implyRightOr' (h : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ ψ ➝ (φ ⋎ χ) := by
  apply deduct';
  apply or₂';
  apply deductInv;
  exact of h;
omit [DecidableEq F] in lemma imply_right_or'! (h : 𝓢 ⊢! ψ ➝ χ) : 𝓢 ⊢! ψ ➝ (φ ⋎ χ) := ⟨implyRightOr' h.some⟩


def implyRightAnd (hq : 𝓢 ⊢ φ ➝ ψ) (hr : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ φ ➝ ψ ⋏ χ := by
  apply deduct';
  replace hq : [] ⊢[𝓢] φ ➝ ψ := of hq;
  replace hr : [] ⊢[𝓢] φ ➝ χ := of hr;
  exact and₃' (mdp' hq FiniteContext.id) (mdp' hr FiniteContext.id)
lemma imply_right_and! (hq : 𝓢 ⊢! φ ➝ ψ) (hr : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! φ ➝ ψ ⋏ χ := ⟨implyRightAnd hq.some hr.some⟩

omit [DecidableEq F] in lemma imply_left_and_comm'! (d : 𝓢 ⊢! φ ⋏ ψ ➝ χ) : 𝓢 ⊢! ψ ⋏ φ ➝ χ := imp_trans''! and_comm! d

lemma dhyp_and_left! (h : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! (ψ ⋏ φ) ➝ χ := by
  apply and_imply_iff_imply_imply'!.mpr;
  apply deduct'!;
  exact FiniteContext.of'! (Γ := [ψ]) h;

lemma dhyp_and_right! (h : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! (φ ⋏ ψ) ➝ χ := imp_trans''! and_comm! (dhyp_and_left! h)

lemma cut! (d₁ : 𝓢 ⊢! φ₁ ⋏ c ➝ ψ₁) (d₂ : 𝓢 ⊢! φ₂ ➝ c ⋎ ψ₂) : 𝓢 ⊢! φ₁ ⋏ φ₂ ➝ ψ₁ ⋎ ψ₂ := by
  apply deduct'!;
  exact or₃'''! (imply_left_or'! $ of'! (and_imply_iff_imply_imply'!.mp d₁) ⨀ (and₁'! id!)) or₂! (of'! d₂ ⨀ and₂'! id!);


def orComm : 𝓢 ⊢ φ ⋎ ψ ➝ ψ ⋎ φ := by
  apply deduct';
  exact or₃''' or₂ or₁ $ FiniteContext.id
omit [DecidableEq F] in lemma or_comm! : 𝓢 ⊢! φ ⋎ ψ ➝ ψ ⋎ φ := ⟨orComm⟩

def orComm' (h : 𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ ψ ⋎ φ := orComm ⨀ h
omit [DecidableEq F] in lemma or_comm'! (h : 𝓢 ⊢! φ ⋎ ψ) : 𝓢 ⊢! ψ ⋎ φ := ⟨orComm' h.some⟩

omit [DecidableEq F] in
lemma or_assoc'! : 𝓢 ⊢! φ ⋎ (ψ ⋎ χ) ↔ 𝓢 ⊢! (φ ⋎ ψ) ⋎ χ := by
  constructor;
  . intro h;
    exact or₃'''!
      (imply_left_or'! $ imply_left_or'! imp_id!)
      (by
        apply provable_iff_provable.mpr;
        apply deduct_iff.mpr;
        exact or₃'''! (imply_left_or'! $ imply_right_or'! imp_id!) (imply_right_or'! imp_id!) id!;
      )
      h;
  . intro h;
    exact or₃'''!
      (by
        apply provable_iff_provable.mpr;
        apply deduct_iff.mpr;
        exact or₃'''! (imply_left_or'! imp_id!) (imply_right_or'! $ imply_left_or'! imp_id!) id!;
      )
      (imply_right_or'! $ imply_right_or'! imp_id!)
      h;

omit [DecidableEq F] in
lemma and_assoc! : 𝓢 ⊢! (φ ⋏ ψ) ⋏ χ ⭤ φ ⋏ (ψ ⋏ χ) := by
  apply iff_intro!;
  . apply FiniteContext.deduct'!;
    have hp : [(φ ⋏ ψ) ⋏ χ] ⊢[𝓢]! φ := and₁'! $ and₁'! id!;
    have hq : [(φ ⋏ ψ) ⋏ χ] ⊢[𝓢]! ψ := and₂'! $ and₁'! id!;
    have hr : [(φ ⋏ ψ) ⋏ χ] ⊢[𝓢]! χ := and₂'! id!;
    exact and₃'! hp (and₃'! hq hr);
  . apply FiniteContext.deduct'!;
    have hp : [φ ⋏ (ψ ⋏ χ)] ⊢[𝓢]! φ := and₁'! id!;
    have hq : [φ ⋏ (ψ ⋏ χ)] ⊢[𝓢]! ψ := and₁'! $ and₂'! id!;
    have hr : [φ ⋏ (ψ ⋏ χ)] ⊢[𝓢]! χ := and₂'! $ and₂'! id!;
    apply and₃'!;
    . exact and₃'! hp hq;
    . exact hr;

def andReplaceLeft' (hc : 𝓢 ⊢ φ ⋏ ψ) (h : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ χ ⋏ ψ := and₃' (h ⨀ and₁' hc) (and₂' hc)
omit [DecidableEq F] in lemma and_replace_left'! (hc : 𝓢 ⊢! φ ⋏ ψ) (h : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! χ ⋏ ψ := ⟨andReplaceLeft' hc.some h.some⟩

def andReplaceLeft (h : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ φ ⋏ ψ ➝ χ ⋏ ψ := by
  apply deduct';
  exact andReplaceLeft' FiniteContext.id (of h)
omit [DecidableEq F] in lemma and_replace_left! (h : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! φ ⋏ ψ ➝ χ ⋏ ψ := ⟨andReplaceLeft h.some⟩


def andReplaceRight' (hc : 𝓢 ⊢ φ ⋏ ψ) (h : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ φ ⋏ χ := and₃' (and₁' hc) (h ⨀ and₂' hc)
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


def orReplaceLeft' (hc : 𝓢 ⊢ φ ⋎ ψ) (hp : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ χ ⋎ ψ := or₃''' (impTrans'' hp or₁) (or₂) hc
omit [DecidableEq F] in lemma or_replace_left'! (hc : 𝓢 ⊢! φ ⋎ ψ) (hp : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! χ ⋎ ψ := ⟨orReplaceLeft' hc.some hp.some⟩

def orReplaceLeft (hp : 𝓢 ⊢ φ ➝ χ) : 𝓢 ⊢ φ ⋎ ψ ➝ χ ⋎ ψ := by
  apply deduct';
  exact orReplaceLeft' FiniteContext.id (of hp)
omit [DecidableEq F] in lemma or_replace_left! (hp : 𝓢 ⊢! φ ➝ χ) : 𝓢 ⊢! φ ⋎ ψ ➝ χ ⋎ ψ := ⟨orReplaceLeft hp.some⟩


def orReplaceRight' (hc : 𝓢 ⊢ φ ⋎ ψ) (hq : 𝓢 ⊢ ψ ➝ χ) : 𝓢 ⊢ φ ⋎ χ := or₃''' (or₁) (impTrans'' hq or₂) hc
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
  apply iffIntro;
  . exact orReplace (and₁' hp) (and₁' hq);
  . exact orReplace (and₂' hp) (and₂' hq);
omit [DecidableEq F] in lemma or_replace_iff! (hp : 𝓢 ⊢! φ₁ ⭤ φ₂) (hq : 𝓢 ⊢! ψ₁ ⭤ ψ₂) : 𝓢 ⊢! φ₁ ⋎ ψ₁ ⭤ φ₂ ⋎ ψ₂ := ⟨orReplaceIff hp.some hq.some⟩

omit [DecidableEq F] in
lemma or_assoc! : 𝓢 ⊢! φ ⋎ (ψ ⋎ χ) ⭤ (φ ⋎ ψ) ⋎ χ := by
  apply iff_intro!;
  . exact deduct'! $ or_assoc'!.mp id!;
  . exact deduct'! $ or_assoc'!.mpr id!;

omit [DecidableEq F] in
lemma or_replace_right_iff! (d : 𝓢 ⊢! ψ ⭤ χ) : 𝓢 ⊢! φ ⋎ ψ ⭤ φ ⋎ χ := by
  apply iff_intro!;
  . apply or_replace_right!; exact and₁'! d;
  . apply or_replace_right!; exact and₂'! d;

omit [DecidableEq F] in
lemma or_replace_left_iff! (d : 𝓢 ⊢! φ ⭤ χ) : 𝓢 ⊢! φ ⋎ ψ ⭤ χ ⋎ ψ := by
  apply iff_intro!;
  . apply or_replace_left!; exact and₁'! d;
  . apply or_replace_left!; exact and₂'! d;


def andReplaceIff (hp : 𝓢 ⊢ φ₁ ⭤ φ₂) (hq : 𝓢 ⊢ ψ₁ ⭤ ψ₂) : 𝓢 ⊢ φ₁ ⋏ ψ₁ ⭤ φ₂ ⋏ ψ₂ := by
  apply iffIntro;
  . exact andReplace (and₁' hp) (and₁' hq);
  . exact andReplace (and₂' hp) (and₂' hq);
omit [DecidableEq F] in lemma and_replace_iff! (hp : 𝓢 ⊢! φ₁ ⭤ φ₂) (hq : 𝓢 ⊢! ψ₁ ⭤ ψ₂) : 𝓢 ⊢! φ₁ ⋏ ψ₁ ⭤ φ₂ ⋏ ψ₂ := ⟨andReplaceIff hp.some hq.some⟩


def impReplaceIff (hp : 𝓢 ⊢ φ₁ ⭤ φ₂) (hq : 𝓢 ⊢ ψ₁ ⭤ ψ₂) : 𝓢 ⊢ (φ₁ ➝ ψ₁) ⭤ (φ₂ ➝ ψ₂) := by
  apply iffIntro;
  . apply deduct'; exact impTrans'' (of $ and₂' hp) $ impTrans'' (FiniteContext.id) (of $ and₁' hq);
  . apply deduct'; exact impTrans'' (of $ and₁' hp) $ impTrans'' (FiniteContext.id) (of $ and₂' hq);
omit [DecidableEq F] in lemma imp_replace_iff! (hp : 𝓢 ⊢! φ₁ ⭤ φ₂) (hq : 𝓢 ⊢! ψ₁ ⭤ ψ₂) : 𝓢 ⊢! (φ₁ ➝ ψ₁) ⭤ (φ₂ ➝ ψ₂) := ⟨impReplaceIff hp.some hq.some⟩

omit [DecidableEq F] in
lemma imp_replace_iff!' (hp : 𝓢 ⊢! φ₁ ⭤ φ₂) (hq : 𝓢 ⊢! ψ₁ ⭤ ψ₂) : 𝓢 ⊢! φ₁ ➝ ψ₁ ↔ 𝓢 ⊢! φ₂ ➝ ψ₂ :=
  provable_iff_of_iff (imp_replace_iff! hp hq)

def dni : 𝓢 ⊢ φ ➝ ∼∼φ := by
  apply deduct';
  apply neg_equiv'.mpr;
  apply deduct;
  exact bot_of_mem_either (φ := φ) (by simp) (by simp);
@[simp] lemma dni! : 𝓢 ⊢! φ ➝ ∼∼φ := ⟨dni⟩

def dni' (b : 𝓢 ⊢ φ) : 𝓢 ⊢ ∼∼φ := dni ⨀ b
lemma dni'! (b : 𝓢 ⊢! φ) : 𝓢 ⊢! ∼∼φ := ⟨dni' b.some⟩


def dniOr' (d : 𝓢 ⊢ φ ⋎ ψ) : 𝓢 ⊢ ∼∼φ ⋎ ∼∼ψ := or₃''' (impTrans'' dni or₁) (impTrans'' dni or₂) d
lemma dni_or'! (d : 𝓢 ⊢! φ ⋎ ψ) : 𝓢 ⊢! ∼∼φ ⋎ ∼∼ψ := ⟨dniOr' d.some⟩

def dniAnd' (d : 𝓢 ⊢ φ ⋏ ψ) : 𝓢 ⊢ ∼∼φ ⋏ ∼∼ψ := and₃' (dni' $ and₁' d) (dni' $ and₂' d)
lemma dni_and'! (d : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! ∼∼φ ⋏ ∼∼ψ := ⟨dniAnd' d.some⟩

def falsumDNE : 𝓢 ⊢ ∼∼⊥ ➝ ⊥ := by
  apply deduct'
  have d₁ : [∼∼⊥] ⊢[𝓢] ∼⊥ ➝ ⊥ := neg_equiv'.mp byAxm₀
  have d₂ : [∼∼⊥] ⊢[𝓢] ∼⊥ := neg_equiv'.mpr (impId ⊥)
  exact d₁ ⨀ d₂

def falsumDN : 𝓢 ⊢ ∼∼⊥ ⭤ ⊥ := andIntro falsumDNE dni

def dn [HasAxiomDNE 𝓢] : 𝓢 ⊢ φ ⭤ ∼∼φ := iffIntro dni dne
@[simp] lemma dn! [HasAxiomDNE 𝓢] : 𝓢 ⊢! φ ⭤ ∼∼φ := ⟨dn⟩


def contra₀ : 𝓢 ⊢ (φ ➝ ψ) ➝ (∼ψ ➝ ∼φ) := by
  apply deduct';
  apply deduct;
  apply neg_equiv'.mpr;
  apply deduct;
  have dp  : [φ, ∼ψ, φ ➝ ψ] ⊢[𝓢] φ := FiniteContext.byAxm;
  have dpq : [φ, ∼ψ, φ ➝ ψ] ⊢[𝓢] φ ➝ ψ := FiniteContext.byAxm;
  have dq  : [φ, ∼ψ, φ ➝ ψ] ⊢[𝓢] ψ := dpq ⨀ dp;
  have dnq : [φ, ∼ψ, φ ➝ ψ] ⊢[𝓢] ψ ➝ ⊥ := neg_equiv'.mp $ FiniteContext.byAxm;
  exact dnq ⨀ dq;
@[simp] def contra₀! : 𝓢 ⊢! (φ ➝ ψ) ➝ (∼ψ ➝ ∼φ) := ⟨contra₀⟩

def contra₀' (b : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ ∼ψ ➝ ∼φ := contra₀ ⨀ b
lemma contra₀'! (b : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! ∼ψ ➝ ∼φ := ⟨contra₀' b.some⟩

def contra₀x2' (b : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ ∼∼φ ➝ ∼∼ψ := contra₀' $ contra₀' b
lemma contra₀x2'! (b : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! ∼∼φ ➝ ∼∼ψ := ⟨contra₀x2' b.some⟩

def contra₀x2 : 𝓢 ⊢ (φ ➝ ψ) ➝ (∼∼φ ➝ ∼∼ψ) := deduct' $ contra₀x2' FiniteContext.id
@[simp] lemma contra₀x2! : 𝓢 ⊢! (φ ➝ ψ) ➝ (∼∼φ ➝ ∼∼ψ) := ⟨contra₀x2⟩


def contra₁' (b : 𝓢 ⊢ φ ➝ ∼ψ) : 𝓢 ⊢ ψ ➝ ∼φ := impTrans'' dni (contra₀' b)
lemma contra₁'! (b : 𝓢 ⊢! φ ➝ ∼ψ) : 𝓢 ⊢! ψ ➝ ∼φ := ⟨contra₁' b.some⟩

def contra₁ : 𝓢 ⊢ (φ ➝ ∼ψ) ➝ (ψ ➝ ∼φ) := deduct' $ contra₁' FiniteContext.id
lemma contra₁! : 𝓢 ⊢! (φ ➝ ∼ψ) ➝ (ψ ➝ ∼φ) := ⟨contra₁⟩


def contra₂' [HasAxiomDNE 𝓢] (b : 𝓢 ⊢ ∼φ ➝ ψ) : 𝓢 ⊢ ∼ψ ➝ φ := impTrans'' (contra₀' b) dne
lemma contra₂'! [HasAxiomDNE 𝓢] (b : 𝓢 ⊢! ∼φ ➝ ψ) : 𝓢 ⊢! ∼ψ ➝ φ := ⟨contra₂' b.some⟩

def contra₂ [HasAxiomDNE 𝓢] : 𝓢 ⊢ (∼φ ➝ ψ) ➝ (∼ψ ➝ φ) := deduct' $ contra₂' FiniteContext.id
@[simp] lemma contra₂! [HasAxiomDNE 𝓢] : 𝓢 ⊢! (∼φ ➝ ψ) ➝ (∼ψ ➝ φ) := ⟨contra₂⟩


def contra₃' [HasAxiomDNE 𝓢] (b : 𝓢 ⊢ ∼φ ➝ ∼ψ) : 𝓢 ⊢ ψ ➝ φ := impTrans'' dni (contra₂' b)
lemma contra₃'! [HasAxiomDNE 𝓢] (b : 𝓢 ⊢! ∼φ ➝ ∼ψ) : 𝓢 ⊢! ψ ➝ φ := ⟨contra₃' b.some⟩

def contra₃ [HasAxiomDNE 𝓢] : 𝓢 ⊢ (∼φ ➝ ∼ψ) ➝ (ψ ➝ φ) :=  deduct' $ contra₃' FiniteContext.id
@[simp] lemma contra₃! [HasAxiomDNE 𝓢] : 𝓢 ⊢! (∼φ ➝ ∼ψ) ➝ (ψ ➝ φ) := ⟨contra₃⟩


def negReplaceIff' (b : 𝓢 ⊢ φ ⭤ ψ) : 𝓢 ⊢ ∼φ ⭤ ∼ψ := iffIntro (contra₀' $ and₂' b) (contra₀' $ and₁' b)
lemma neg_replace_iff'! (b : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! ∼φ ⭤ ∼ψ := ⟨negReplaceIff' b.some⟩


def iffNegLeftToRight' [HasAxiomDNE 𝓢] (h : 𝓢 ⊢ φ ⭤ ∼ψ) : 𝓢 ⊢ ∼φ ⭤ ψ := by
  apply iffIntro;
  . apply contra₂' $  and₂' h;
  . apply contra₁' $  and₁' h;
lemma iff_neg_left_to_right'! [HasAxiomDNE 𝓢] (h : 𝓢 ⊢! φ ⭤ ∼ψ) : 𝓢 ⊢! ∼φ ⭤ ψ := ⟨iffNegLeftToRight' h.some⟩

def iffNegRightToLeft' [HasAxiomDNE 𝓢] (h : 𝓢 ⊢ ∼φ ⭤ ψ) : 𝓢 ⊢ φ ⭤ ∼ψ := iffComm' $ iffNegLeftToRight' $ iffComm' h
lemma iff_neg_right_to_left'! [HasAxiomDNE 𝓢] (h : 𝓢 ⊢! ∼φ ⭤ ψ) : 𝓢 ⊢! φ ⭤ ∼ψ := ⟨iffNegRightToLeft' h.some⟩

section NegationEquiv

variable [Entailment.NegationEquiv 𝓢]

def negneg_equiv : 𝓢 ⊢ ∼∼φ ⭤ ((φ ➝ ⊥) ➝ ⊥) := by
  apply iffIntro;
  . exact impTrans'' (by apply contra₀'; exact and₂' neg_equiv) (and₁' neg_equiv)
  . exact impTrans'' (and₂' neg_equiv) (by apply contra₀'; exact and₁' neg_equiv)
@[simp] lemma negneg_equiv! : 𝓢 ⊢! ∼∼φ ⭤ ((φ ➝ ⊥) ➝ ⊥) := ⟨negneg_equiv⟩

def negneg_equiv_dne [HasAxiomDNE 𝓢] : 𝓢 ⊢ φ ⭤ ((φ ➝ ⊥) ➝ ⊥) := iffTrans'' dn negneg_equiv
lemma negneg_equiv_dne! [HasAxiomDNE 𝓢] : 𝓢 ⊢! φ ⭤ ((φ ➝ ⊥) ➝ ⊥) := ⟨negneg_equiv_dne⟩

end NegationEquiv

def elim_contra_neg [HasAxiomElimContra 𝓢] : 𝓢 ⊢ ((ψ ➝ ⊥) ➝ (φ ➝ ⊥)) ➝ (φ ➝ ψ) := by
  refine impTrans'' ?_ elim_contra;
  apply deduct';
  exact impTrans'' (impTrans'' (and₁' neg_equiv) FiniteContext.byAxm) (and₂' neg_equiv);
@[simp] lemma elim_contra_neg! [HasAxiomElimContra 𝓢] : 𝓢 ⊢! ((ψ ➝ ⊥) ➝ (φ ➝ ⊥)) ➝ (φ ➝ ψ) := ⟨elim_contra_neg⟩


def tne : 𝓢 ⊢ ∼(∼∼φ) ➝ ∼φ := contra₀' dni
@[simp] lemma tne! : 𝓢 ⊢! ∼(∼∼φ) ➝ ∼φ := ⟨tne⟩

def tne' (b : 𝓢 ⊢ ∼(∼∼φ)) : 𝓢 ⊢ ∼φ := tne ⨀ b
lemma tne'! (b : 𝓢 ⊢! ∼(∼∼φ)) : 𝓢 ⊢! ∼φ := ⟨tne' b.some⟩

def tneIff : 𝓢 ⊢ ∼∼∼φ ⭤ ∼φ := andIntro tne dni

def implyLeftReplace (h : 𝓢 ⊢ ψ ➝ φ) : 𝓢 ⊢ (φ ➝ χ) ➝ (ψ ➝ χ) := by
  apply deduct';
  exact impTrans'' (of h) id;
omit [DecidableEq F] in lemma replace_imply_left! (h : 𝓢 ⊢! ψ ➝ φ) : 𝓢 ⊢! (φ ➝ χ) ➝ (ψ ➝ χ) := ⟨implyLeftReplace h.some⟩

omit [DecidableEq F] in
lemma replace_imply_left_by_iff'! (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! φ ➝ χ ↔ 𝓢 ⊢! ψ ➝ χ := by
  constructor;
  . exact imp_trans''! $ and₂'! h;
  . exact imp_trans''! $ and₁'! h;

omit [DecidableEq F] in
lemma replace_imply_right_by_iff'! (h : 𝓢 ⊢! φ ⭤ ψ) : 𝓢 ⊢! χ ➝ φ ↔ 𝓢 ⊢! χ ➝ ψ := by
  constructor;
  . intro hrp; exact imp_trans''! hrp $ and₁'! h;
  . intro hrq; exact imp_trans''! hrq $ and₂'! h;


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

def p_pq_q : 𝓢 ⊢ φ ➝ (φ ➝ ψ) ➝ ψ := impSwap' $ impId _
lemma p_pq_q! : 𝓢 ⊢! φ ➝ (φ ➝ ψ) ➝ ψ := ⟨p_pq_q⟩

def dhyp_imp' (h : 𝓢 ⊢ φ ➝ ψ) : 𝓢 ⊢ (χ ➝ φ) ➝ (χ ➝ ψ) := imply₂ ⨀ (imply₁' h)
omit [DecidableEq F] in lemma dhyp_imp'! (h : 𝓢 ⊢! φ ➝ ψ) : 𝓢 ⊢! (χ ➝ φ) ➝ (χ ➝ ψ) := ⟨dhyp_imp' h.some⟩

def rev_dhyp_imp' (h : 𝓢 ⊢ ψ ➝ φ) : 𝓢 ⊢ (φ ➝ χ) ➝ (ψ ➝ χ) := impSwap' $ impTrans'' h p_pq_q
lemma rev_dhyp_imp'! (h : 𝓢 ⊢! ψ ➝ φ) : 𝓢 ⊢! (φ ➝ χ) ➝ (ψ ➝ χ) := ⟨rev_dhyp_imp' h.some⟩

-- TODO: Actually this can be computable but it's too slow.
noncomputable def dnDistributeImply : 𝓢 ⊢ ∼∼(φ ➝ ψ) ➝ (∼∼φ ➝ ∼∼ψ) := by
  apply impSwap';
  apply deduct';
  exact impTrans'' (contra₀x2' $ deductInv $ of $ impSwap' $ contra₀x2) tne;
@[simp] lemma dn_distribute_imply! : 𝓢 ⊢! ∼∼(φ ➝ ψ) ➝ (∼∼φ ➝ ∼∼ψ) := ⟨dnDistributeImply⟩

noncomputable def dnDistributeImply' (b : 𝓢 ⊢ ∼∼(φ ➝ ψ)) : 𝓢 ⊢ ∼∼φ ➝ ∼∼ψ := dnDistributeImply ⨀ b
lemma dn_distribute_imply'! (b : 𝓢 ⊢! ∼∼(φ ➝ ψ)) : 𝓢 ⊢! ∼∼φ ➝ ∼∼ψ := ⟨dnDistributeImply' b.some⟩


def introFalsumOfAnd' (h : 𝓢 ⊢ φ ⋏ ∼φ) : 𝓢 ⊢ ⊥ := (neg_equiv'.mp $ and₂' h) ⨀ (and₁' h)
omit [DecidableEq F] in lemma intro_falsum_of_and'! (h : 𝓢 ⊢! φ ⋏ ∼φ) : 𝓢 ⊢! ⊥ := ⟨introFalsumOfAnd' h.some⟩
/-- Law of contradiction -/
alias lac'! := intro_falsum_of_and'!

def introFalsumOfAnd : 𝓢 ⊢ φ ⋏ ∼φ ➝ ⊥ := by
  apply deduct';
  exact introFalsumOfAnd' (φ := φ) $ FiniteContext.id
omit [DecidableEq F] in @[simp] lemma intro_bot_of_and! : 𝓢 ⊢! φ ⋏ ∼φ ➝ ⊥ := ⟨introFalsumOfAnd⟩
/-- Law of contradiction -/
alias lac! := intro_bot_of_and!



def implyOfNotOr [HasAxiomEFQ 𝓢] : 𝓢 ⊢ (∼φ ⋎ ψ) ➝ (φ ➝ ψ) := or₃'' (by
    apply emptyPrf;
    apply deduct;
    apply deduct;
    exact efq_of_mem_either (φ := φ) (by simp) (by simp)
  ) imply₁
@[simp] lemma imply_of_not_or! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! (∼φ ⋎ ψ) ➝ (φ ➝ ψ) := ⟨implyOfNotOr⟩

def implyOfNotOr' [HasAxiomEFQ 𝓢] (b : 𝓢 ⊢ ∼φ ⋎ ψ) : 𝓢 ⊢ φ ➝ ψ := implyOfNotOr ⨀ b
lemma imply_of_not_or'! [HasAxiomEFQ 𝓢] (b : 𝓢 ⊢! ∼φ ⋎ ψ) : 𝓢 ⊢! φ ➝ ψ := ⟨implyOfNotOr' b.some⟩


def demorgan₁ : 𝓢 ⊢ (∼φ ⋎ ∼ψ) ➝ ∼(φ ⋏ ψ) := or₃'' (contra₀' and₁) (contra₀' and₂)
@[simp] lemma demorgan₁! : 𝓢 ⊢! (∼φ ⋎ ∼ψ) ➝ ∼(φ ⋏ ψ) := ⟨demorgan₁⟩

def demorgan₁' (d : 𝓢 ⊢ ∼φ ⋎ ∼ψ) : 𝓢 ⊢ ∼(φ ⋏ ψ)  := demorgan₁ ⨀ d
lemma demorgan₁'! (d : 𝓢 ⊢! ∼φ ⋎ ∼ψ) : 𝓢 ⊢! ∼(φ ⋏ ψ) := ⟨demorgan₁' d.some⟩


def demorgan₂ : 𝓢 ⊢ (∼φ ⋏ ∼ψ) ➝ ∼(φ ⋎ ψ) := by
  apply andImplyIffImplyImply'.mpr;
  apply deduct';
  apply deduct;
  apply neg_equiv'.mpr;
  apply deduct;
  exact or₃''' (neg_equiv'.mp FiniteContext.byAxm) (neg_equiv'.mp FiniteContext.byAxm) (FiniteContext.byAxm (φ := φ ⋎ ψ));
@[simp] lemma demorgan₂! : 𝓢 ⊢! ∼φ ⋏ ∼ψ ➝ ∼(φ ⋎ ψ) := ⟨demorgan₂⟩

def demorgan₂' (d : 𝓢 ⊢ ∼φ ⋏ ∼ψ) : 𝓢 ⊢ ∼(φ ⋎ ψ) := demorgan₂ ⨀ d
lemma demorgan₂'! (d : 𝓢 ⊢! ∼φ ⋏ ∼ψ) : 𝓢 ⊢! ∼(φ ⋎ ψ) := ⟨demorgan₂' d.some⟩


def demorgan₃ : 𝓢 ⊢ ∼(φ ⋎ ψ) ➝ (∼φ ⋏ ∼ψ) := by
  apply deduct';
  exact and₃' (deductInv $ contra₀' $ or₁) (deductInv $ contra₀' $ or₂)
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
  apply dne';
  apply neg_equiv'.mpr;
  apply deduct';
  have d₁ : [∼(∼φ ⋎ ψ)] ⊢[𝓢] ∼∼φ ⋏ ∼ψ := demorgan₃' $ FiniteContext.id;
  have d₂ : [∼(∼φ ⋎ ψ)] ⊢[𝓢] ∼φ ➝ ⊥ := neg_equiv'.mp $ and₁' d₁;
  have d₃ : [∼(∼φ ⋎ ψ)] ⊢[𝓢] ∼φ := (of (Γ := [∼(∼φ ⋎ ψ)]) $ contra₀' d) ⨀ (and₂' d₁);
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
  apply neg_equiv'.mpr;
  exact impTrans''
    (by
      apply deductInv;
      apply andImplyIffImplyImply'.mp;
      apply deduct;
      have d₁ : [(∼∼φ ➝ ∼∼ψ) ⋏ ∼(φ ➝ ψ)] ⊢[𝓢] ∼∼φ ➝ ∼∼ψ := and₁' (ψ := ∼(φ ➝ ψ)) $ FiniteContext.id;
      have d₂ : [(∼∼φ ➝ ∼∼ψ) ⋏ ∼(φ ➝ ψ)] ⊢[𝓢] ∼∼φ ⋏ ∼ψ := demorgan₃' $ (contra₀' implyOfNotOr) ⨀ (and₂' (φ := (∼∼φ ➝ ∼∼ψ)) $ FiniteContext.id)
      exact and₃' (and₂' d₂) (d₁ ⨀ (and₁' d₂))
    )
    (introFalsumOfAnd (φ := ∼ψ));

@[simp] lemma dn_collect_imply! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! (∼∼φ ➝ ∼∼ψ) ➝ ∼∼(φ ➝ ψ) := ⟨dnCollectImply⟩

-- TODO: Actually this can be computable but it's too slow.
noncomputable def dnCollectImply' [HasAxiomEFQ 𝓢] (b : 𝓢 ⊢ ∼∼φ ➝ ∼∼ψ) : 𝓢 ⊢ ∼∼(φ ➝ ψ) := dnCollectImply ⨀ b
lemma dn_collect_imply'! [HasAxiomEFQ 𝓢] (b : 𝓢 ⊢! ∼∼φ ➝ ∼∼ψ) : 𝓢 ⊢! ∼∼(φ ➝ ψ) := ⟨dnCollectImply' b.some⟩


def andImplyAndOfImply {φ ψ φ' ψ' : F} (bp : 𝓢 ⊢ φ ➝ φ') (bq : 𝓢 ⊢ ψ ➝ ψ') : 𝓢 ⊢ φ ⋏ ψ ➝ φ' ⋏ ψ' :=
  deduct' <| andIntro
    (deductInv' <| impTrans'' and₁ bp)
    (deductInv' <| impTrans'' and₂ bq)

def andIffAndOfIff {φ ψ φ' ψ' : F} (bp : 𝓢 ⊢ φ ⭤ φ') (bq : 𝓢 ⊢ ψ ⭤ ψ') : 𝓢 ⊢ φ ⋏ ψ ⭤ φ' ⋏ ψ' :=
  iffIntro (andImplyAndOfImply (andLeft bp) (andLeft bq)) (andImplyAndOfImply (andRight bp) (andRight bq))


section Instantinate

instance [HasAxiomDNE 𝓢] : HasAxiomEFQ 𝓢 where
  efq φ := by
    apply contra₃';
    exact impTrans'' (and₁' neg_equiv) $ impTrans'' (impSwap' imply₁) (and₂' neg_equiv);


-- TODO: Actually this can be computable but it's too slow.
noncomputable instance [HasAxiomDNE 𝓢] : HasAxiomLEM 𝓢 where
  lem _ := dneOr $ NotOrOfImply' dni

instance [HasAxiomEFQ 𝓢] [HasAxiomLEM 𝓢] : HasAxiomDNE 𝓢 where
  dne φ := by
    apply deduct';
    exact or₃''' (impId _) (by
      apply deduct;
      have nnp : [∼φ, ∼∼φ] ⊢[𝓢] ∼φ ➝ ⊥ := neg_equiv'.mp $ FiniteContext.byAxm;
      have np : [∼φ, ∼∼φ] ⊢[𝓢] ∼φ := FiniteContext.byAxm;
      exact efq' $ nnp ⨀ np;
    ) $ of lem;;

instance [HasAxiomLEM 𝓢] : HasAxiomWeakLEM 𝓢 where
  wlem φ := lem (φ := ∼φ);

instance [HasAxiomEFQ 𝓢] [HasAxiomLEM 𝓢] : HasAxiomDummett 𝓢 where
  dummett φ ψ := by
    have d₁ : 𝓢 ⊢ φ ➝ ((φ ➝ ψ) ⋎ (ψ ➝ φ)) := impTrans'' imply₁ or₂;
    have d₂ : 𝓢 ⊢ ∼φ ➝ ((φ ➝ ψ) ⋎ (ψ ➝ φ)) := impTrans'' efq_imply_not₁ or₁;
    exact or₃''' d₁ d₂ lem;

instance [HasAxiomEFQ 𝓢] [HasAxiomDummett 𝓢] : HasAxiomWeakLEM 𝓢 where
  wlem φ := by
    haveI : 𝓢 ⊢ (φ ➝ ∼φ) ⋎ (∼φ ➝ φ) := dummett;
    exact or₃''' (by
      apply deduct';
      apply or₁';
      apply neg_equiv'.mpr;
      apply deduct;
      haveI d₁ : [φ, φ ➝ ∼φ] ⊢[𝓢] φ := FiniteContext.byAxm;
      haveI d₂ : [φ, φ ➝ ∼φ] ⊢[𝓢] φ ➝ ∼φ := FiniteContext.byAxm;
      have := neg_equiv'.mp $ d₂ ⨀ d₁;
      exact this ⨀ d₁;
    ) (by
      apply deduct';
      apply or₂';
      apply neg_equiv'.mpr;
      apply deduct;
      haveI d₁ : [∼φ, ∼φ ➝ φ] ⊢[𝓢] ∼φ := FiniteContext.byAxm;
      haveI d₂ : [∼φ, ∼φ ➝ φ] ⊢[𝓢] ∼φ ➝ φ := FiniteContext.byAxm;
      haveI := d₂ ⨀ d₁;
      exact (neg_equiv'.mp d₁) ⨀ this;
    ) this;

noncomputable instance [HasAxiomDNE 𝓢] : HasAxiomPeirce 𝓢 where
  peirce φ ψ := by
    refine or₃''' imply₁ ?_ lem;
    apply deduct';
    apply deduct;
    refine (FiniteContext.byAxm (φ := (φ ➝ ψ) ➝ φ)) ⨀ ?_;
    apply deduct;
    apply efq_of_mem_either (by aesop) (by aesop)

instance [HasAxiomDNE 𝓢] : HasAxiomElimContra 𝓢 where
  elim_contra φ ψ := by
    apply deduct';
    have : [∼ψ ➝ ∼φ] ⊢[𝓢] ∼ψ ➝ ∼φ := FiniteContext.byAxm;
    exact contra₃' this;

end Instantinate

noncomputable def implyIffNotOr [HasAxiomDNE 𝓢] : 𝓢 ⊢ (φ ➝ ψ) ⭤ (∼φ ⋎ ψ) := iffIntro
  NotOrOfImply (deduct' (orCases efq_imply_not₁ imply₁ byAxm₀))

noncomputable def imply_iff_not_or! [HasAxiomDNE 𝓢] : 𝓢 ⊢! (φ ➝ ψ) ⭤ (∼φ ⋎ ψ) := ⟨implyIffNotOr⟩

def conjIffConj : (Γ : List F) → 𝓢 ⊢ ⋀Γ ⭤ Γ.conj
  | []          => iffId ⊤
  | [_]         => iffIntro (deduct' <| andIntro FiniteContext.id verum) and₁
  | φ :: ψ :: Γ => andIffAndOfIff (iffId φ) (conjIffConj (ψ :: Γ))
omit [DecidableEq F] in @[simp] lemma conjIffConj! : 𝓢 ⊢! ⋀Γ ⭤ Γ.conj := ⟨conjIffConj Γ⟩


omit [DecidableEq F] in lemma implyLeft_conj_eq_conj! : 𝓢 ⊢! Γ.conj ➝ φ ↔ 𝓢 ⊢! ⋀Γ ➝ φ := replace_imply_left_by_iff'! $ iff_comm'! conjIffConj!


lemma generalConj'! (h : φ ∈ Γ) : 𝓢 ⊢! ⋀Γ ➝ φ := replace_imply_left_by_iff'! conjIffConj! |>.mpr (generalConj! h)
lemma generalConj'₂! (h : φ ∈ Γ) (d : 𝓢 ⊢! ⋀Γ) : 𝓢 ⊢! φ := (generalConj'! h) ⨀ d

section Conjunction

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
      . exact and₁'! h;
      . exact ih.mp (and₂'! h);
    . rintro ⟨h₁, h₂⟩;
      exact and₃'! h₁ (ih.mpr h₂);

lemma conjconj_subset! (h : ∀ φ, φ ∈ Γ → φ ∈ Δ) : 𝓢 ⊢! ⋀Δ ➝ ⋀Γ := by
  induction Γ using List.induction_with_singleton with
  | hnil => simp;
  | hsingle => simp_all; exact generalConj'! h;
  | hcons φ Γ hne ih => simp_all; exact imply_right_and! (generalConj'! h.1) ih;

lemma conjconj_provable! (h : ∀ φ, φ ∈ Γ → Δ ⊢[𝓢]! φ) : 𝓢 ⊢! ⋀Δ ➝ ⋀Γ :=
  by induction Γ using List.induction_with_singleton with
  | hnil => exact imply₁'! verum!;
  | hsingle => simp_all; exact provable_iff.mp h;
  | hcons φ Γ hne ih => simp_all; exact imply_right_and! (provable_iff.mp h.1) ih;

lemma conjconj_provable₂! (h : ∀ φ, φ ∈ Γ → Δ ⊢[𝓢]! φ) : Δ ⊢[𝓢]! ⋀Γ := provable_iff.mpr $ conjconj_provable! h

lemma id_conj! (he : ∀ g ∈ Γ, g = φ) : 𝓢 ⊢! φ ➝ ⋀Γ := by
  induction Γ using List.induction_with_singleton with
  | hcons χ Γ h ih =>
    simp_all;
    have ⟨he₁, he₂⟩ := he; subst he₁;
    exact imply_right_and! imp_id! ih;
  | _ => simp_all;

lemma replace_imply_left_conj! (he : ∀ g ∈ Γ, g = φ) (hd : 𝓢 ⊢! ⋀Γ ➝ ψ) : 𝓢 ⊢! φ ➝ ψ := imp_trans''! (id_conj! he) hd

lemma iff_imply_left_cons_conj'! : 𝓢 ⊢! ⋀(φ :: Γ) ➝ ψ ↔ 𝓢 ⊢! φ ⋏ ⋀Γ ➝ ψ := by
  induction Γ with
  | nil =>
    simp [and_imply_iff_imply_imply'!];
    constructor;
    . intro h; apply imp_swap'!; exact imply₁'! h;
    . intro h; exact imp_swap'! h ⨀ verum!;
  | cons ψ ih => simp;

omit [DecidableEq F] in
@[simp] lemma imply_left_concat_conj! : 𝓢 ⊢! ⋀(Γ ++ Δ) ➝ ⋀Γ ⋏ ⋀Δ := by
  apply FiniteContext.deduct'!;
  have : [⋀(Γ ++ Δ)] ⊢[𝓢]! ⋀(Γ ++ Δ) := id!;
  have d := iff_provable_list_conj.mp this;
  apply and₃'!;
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
  . subst e; exact and₂'! id!;
  . exact iff_provable_list_conj.mp (and₁'! id!) ψ (by apply List.mem_remove_iff.mpr; simp_all);

lemma imply_left_remove_conj! (b : 𝓢 ⊢! ⋀Γ ➝ ψ) : 𝓢 ⊢! ⋀(Γ.remove φ) ⋏ φ ➝ ψ := imp_trans''! forthback_conj_remove! b

omit [DecidableEq F] in
lemma iff_concat_conj'! : 𝓢 ⊢! ⋀(Γ ++ Δ) ↔ 𝓢 ⊢! ⋀Γ ⋏ ⋀Δ := by
  constructor;
  . intro h;
    replace h := iff_provable_list_conj.mp h;
    apply and₃'!;
    . apply iff_provable_list_conj.mpr;
      intro φ hp; exact h φ (by simp only [List.mem_append]; left; simpa);
    . apply iff_provable_list_conj.mpr;
      intro φ hp; exact h φ (by simp only [List.mem_append]; right; simpa);
  . intro h;
    apply iff_provable_list_conj.mpr;
    simp only [List.mem_append];
    rintro φ (hp₁ | hp₂);
    . exact (iff_provable_list_conj.mp $ and₁'! h) φ hp₁;
    . exact (iff_provable_list_conj.mp $ and₂'! h) φ hp₂;

omit [DecidableEq F] in
@[simp] lemma iff_concat_conj! : 𝓢 ⊢! ⋀(Γ ++ Δ) ⭤ ⋀Γ ⋏ ⋀Δ := by
  apply iff_intro!;
  . apply deduct'!; apply iff_concat_conj'!.mp; exact id!;
  . apply deduct'!; apply iff_concat_conj'!.mpr; exact id!;

omit [DecidableEq F] in
lemma imply_left_conj_concat! : 𝓢 ⊢! ⋀(Γ ++ Δ) ➝ φ ↔ 𝓢 ⊢! (⋀Γ ⋏ ⋀Δ) ➝ φ := by
  constructor;
  . intro h; exact imp_trans''! (and₂'! iff_concat_conj!) h;
  . intro h; exact imp_trans''! (and₁'! iff_concat_conj!) h;

end Conjunction


section disjunction

omit [DecidableEq F] in
lemma iff_concact_disj! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! ⋁(Γ ++ Δ) ⭤ ⋁Γ ⋎ ⋁Δ := by
  induction Γ using List.induction_with_singleton generalizing Δ <;> induction Δ using List.induction_with_singleton;
  case hnil.hnil =>
    simp_all;
    apply iff_intro!;
    . simp;
    . exact or₃''! efq! efq!;
  case hnil.hsingle =>
    simp_all;
    apply iff_intro!;
    . simp;
    . exact or₃''! efq! imp_id!;
  case hsingle.hnil =>
    simp_all;
    apply iff_intro!;
    . simp;
    . exact or₃''! imp_id! efq!;
  case hcons.hnil =>
    simp_all;
    apply iff_intro!;
    . simp;
    . exact or₃''! imp_id! efq!;
  case hnil.hcons =>
    simp_all;
    apply iff_intro!;
    . simp;
    . exact or₃''! efq! imp_id!;
  case hsingle.hsingle => simp_all;
  case hsingle.hcons => simp_all;
  case hcons.hsingle φ ps hps ihp ψ =>
    simp_all;
    apply iff_trans''! (by
      apply or_replace_right_iff!;
      simpa using @ihp [ψ];
    ) or_assoc!;
  case hcons.hcons φ ps hps ihp ψ qs hqs ihq =>
    simp_all;
    exact iff_trans''! (by
      apply or_replace_right_iff!;
      exact iff_trans''! (@ihp (ψ :: qs)) (by
        apply or_replace_right_iff!;
        simp_all;
      )
    ) or_assoc!;

omit [DecidableEq F] in
lemma iff_concact_disj'! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! ⋁(Γ ++ Δ) ↔ 𝓢 ⊢! ⋁Γ ⋎ ⋁Δ := by
  constructor;
  . intro h; exact (and₁'! iff_concact_disj!) ⨀ h;
  . intro h; exact (and₂'! iff_concact_disj!) ⨀ h;

omit [DecidableEq F] in
lemma implyRight_cons_disj! [HasAxiomEFQ 𝓢] : 𝓢 ⊢! φ ➝ ⋁(ψ :: Γ) ↔ 𝓢 ⊢! φ ➝ ψ ⋎ ⋁Γ := by
  induction Γ with
  | nil =>
    simp;
    constructor;
    . intro h; exact imp_trans''! h or₁!;
    . intro h; exact imp_trans''! h $ or₃''! imp_id! efq!;
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
    . simp_all only [ne_eq, List.remove_cons_self]; exact or₃''! or₁! ih;
    . simp_all [(List.remove_cons_of_ne Γ hpq)];
      by_cases hqΓ : Γ.remove φ = [];
      . simp_all;
        exact or₃''! or₂! (imp_trans''! ih $ or_replace_right! efq!);
      . simp_all;
        exact or₃''! (imp_trans''! or₁! or₂!) (imp_trans''! ih (or_replace_right! or₂!));

lemma disj_allsame! [HasAxiomEFQ 𝓢] (hd : ∀ ψ ∈ Γ, ψ = φ) : 𝓢 ⊢! ⋁Γ ➝ φ := by
  induction Γ using List.induction_with_singleton with
  | hcons ψ Δ hΔ ih =>
    simp_all;
    have ⟨hd₁, hd₂⟩ := hd; subst hd₁;
    apply provable_iff_provable.mpr;
    apply deduct_iff.mpr;
    exact or₃'''! (by simp) (weakening! (by simp) $ provable_iff_provable.mp $ ih) id!
  | _ => simp_all;

lemma disj_allsame'! [HasAxiomEFQ 𝓢] (hd : ∀ ψ ∈ Γ, ψ = φ) (h : 𝓢 ⊢! ⋁Γ) : 𝓢 ⊢! φ := (disj_allsame! hd) ⨀ h

end disjunction

section consistency

variable [HasAxiomEFQ 𝓢]

omit [DecidableEq F] in
lemma inconsistent_of_provable_of_unprovable {φ : F}
    (hp : 𝓢 ⊢! φ) (hn : 𝓢 ⊢! ∼φ) : Inconsistent 𝓢 := by
  have : 𝓢 ⊢! φ ➝ ⊥ := neg_equiv'!.mp hn
  intro ψ; exact efq! ⨀ (this ⨀ hp)

end consistency

end LO.Entailment

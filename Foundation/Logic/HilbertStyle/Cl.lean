import Foundation.Logic.HilbertStyle.Supplemental

namespace LO.Entailment

open Entailment
open FiniteContext

variable {F : Type*} [LogicalConnective F] [DecidableEq F]
         {S : Type*} [Entailment F S]
         {𝓢 : S} [Entailment.Cl 𝓢]
         {φ ψ χ ξ : F}

@[simp]
lemma IIIpIqbNIpNq! : 𝓢 ⊢! ((φ ➝ ψ ➝ ⊥) ➝ ⊥) ➝ ∼(φ ➝ ∼ψ) := by
  apply imp_trans''! (and₂'! neg_equiv!) ?_;
  apply contra₀'!;
  apply dhyp_imp'!;
  apply and₁'! neg_equiv!;

lemma ONpNq_IpNq! (h : 𝓢 ⊢! ∼φ ⋎ ∼ψ) : 𝓢 ⊢! φ ➝ ∼ψ := by
  apply or₃'''! efq_imply_not₁! imply₁! h;

@[simp]
lemma IIIpIqbbApq! : 𝓢 ⊢! ((φ ➝ (ψ ➝ ⊥)) ➝ ⊥) ➝ (φ ⋏ ψ) := by
  apply imp_trans''! IIIpIqbNIpNq! ?_;
  apply contra₂'!
  apply deduct'!;
  have : [∼(φ ⋏ ψ)] ⊢[𝓢]! ∼φ ⋎ ∼ψ := demorgan₄'! $ by_axm!
  exact or₃'''! efq_imply_not₁! imply₁! this;

lemma IIIpIqbb_Apq! (h : 𝓢 ⊢! ((φ ➝ (ψ ➝ ⊥)) ➝ ⊥)) : 𝓢 ⊢! (φ ⋏ ψ) := IIIpIqbbApq! ⨀ h

lemma Apq_IIpIqbb! (b : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! (φ ➝ ψ ➝ ⊥) ➝ ⊥ := by
  apply deduct'!;
  have h₁ : [φ ➝ ψ ➝ ⊥] ⊢[𝓢]! φ := of'! $ and₁'! b;
  have h₂ : [φ ➝ ψ ➝ ⊥] ⊢[𝓢]! ψ := of'! $ and₂'! b;
  have H : [φ ➝ ψ ➝ ⊥] ⊢[𝓢]! φ ➝ ψ ➝ ⊥ := by_axm!;
  exact (H ⨀ h₁) ⨀ h₂;

@[simp]
lemma ApqIIpIqbb! : 𝓢 ⊢! (φ ⋏ ψ) ➝ ((φ ➝ ψ ➝ ⊥) ➝ ⊥) := by
  apply deduct'!;
  apply Apq_IIpIqbb!;
  apply by_axm!;
  simp;

lemma Iqp_Irs_IIprIqs (h₁ : 𝓢 ⊢! ψ ➝ φ) (h₂ : 𝓢 ⊢! χ ➝ ξ) : 𝓢 ⊢! (φ ➝ χ) ➝ (ψ ➝ ξ) := by
  replace h₁ : [ψ, φ ➝ χ] ⊢[𝓢]! ψ ➝ φ := of'! $ h₁;
  replace h₂ : [ψ, φ ➝ χ] ⊢[𝓢]! χ ➝ ξ := of'! $ h₂;
  have h₃ : [ψ, φ ➝ χ] ⊢[𝓢]! φ ➝ χ := by_axm!;
  apply deduct'!;
  apply deduct!;
  exact h₂ ⨀ (h₃ ⨀ (h₁ ⨀ (by_axm!)))

lemma Epq_Ers_EIprIqs! (h₁ : 𝓢 ⊢! φ ⭤ ψ) (h₂ : 𝓢 ⊢! χ ⭤ ξ) : 𝓢 ⊢! (φ ➝ χ) ⭤ (ψ ➝ ξ) := by
  apply and₃'!;
  . apply Iqp_Irs_IIprIqs (and₂'! h₁) (and₁'! h₂);
  . apply Iqp_Irs_IIprIqs (and₁'! h₁) (and₂'! h₂);

@[simp]
lemma IIIpbqOpq! : 𝓢 ⊢! ((φ ➝ ⊥) ➝ ψ) ➝ (φ ⋎ ψ) := by
  apply deduct'!;
  apply or₃'''! or₁! ?_ lem!;
  . apply deduct!;
    apply or₂'!;
    have H₁ : [∼φ, (φ ➝ ⊥) ➝ ψ] ⊢[𝓢]! φ ➝ ⊥ := neg_equiv'!.mp by_axm!;
    have H₂ : [∼φ, (φ ➝ ⊥) ➝ ψ] ⊢[𝓢]! (φ ➝ ⊥) ➝ ψ := by_axm!;
    exact H₂ ⨀ H₁;

@[simp]
lemma IOpqIIpbq! : 𝓢 ⊢! (φ ⋎ ψ) ➝ ((φ ➝ ⊥) ➝ ψ) := by
  apply deduct'!;
  apply deduct!;
  have : [φ ➝ ⊥, φ ⋎ ψ] ⊢[𝓢]! φ ⋎ ψ := by_axm!;
  apply or₃'''! ?_ imp_id! this;
  . apply deduct!;
    refine efq! ⨀ ?_;
    have H₁ : [φ, φ ➝ ⊥, φ ⋎ ψ] ⊢[𝓢]! φ := by_axm!;
    have H₂ : [φ, φ ➝ ⊥, φ ⋎ ψ] ⊢[𝓢]! φ ➝ ⊥ := by_axm!;
    exact H₂ ⨀ H₁;

@[simp]
lemma IIIpbqOpq : 𝓢 ⊢! ((φ ➝ ⊥) ➝ ψ) ➝ (φ ⋎ ψ) := by
  apply deduct'!;
  apply or₃'''! or₁! ?_ lem!;
  . apply deduct!;
    apply or₂'!;
    have H₁ : [∼φ, (φ ➝ ⊥) ➝ ψ] ⊢[𝓢]! φ ➝ ⊥ := neg_equiv'!.mp by_axm!;
    have H₂ : [∼φ, (φ ➝ ⊥) ➝ ψ] ⊢[𝓢]! (φ ➝ ⊥) ➝ ψ := by_axm!;
    exact H₂ ⨀ H₁;

@[simp]
lemma IOpqIIpbq : 𝓢 ⊢! (φ ⋎ ψ) ➝ ((φ ➝ ⊥) ➝ ψ) := by
  apply deduct'!;
  apply deduct!;
  have : [φ ➝ ⊥, φ ⋎ ψ] ⊢[𝓢]! φ ⋎ ψ := by_axm!;
  apply or₃'''! ?_ imp_id! this;
  . apply deduct!;
    refine efq! ⨀ ?_;
    have H₁ : [φ, φ ➝ ⊥, φ ⋎ ψ] ⊢[𝓢]! φ := by_axm!;
    have H₂ : [φ, φ ➝ ⊥, φ ⋎ ψ] ⊢[𝓢]! φ ➝ ⊥ := by_axm!;
    exact H₂ ⨀ H₁;

lemma ENIpqApNq! : 𝓢 ⊢! ∼(φ ➝ ψ) ⭤ (φ ⋏ ∼ψ) := by
  apply and₃'!;
  . apply deduct'!;
    apply and₃'!;
    . apply deductInv'!;
      apply contra₂'!;
      exact efq_imply_not₁!
    . apply deductInv'!;
      apply contra₂'!;
      apply imp_swap'!;
      apply deduct'!;
      exact dne!;
  . apply not_imply_prem''! and₁! and₂!;

lemma NIpq_ApNq! : 𝓢 ⊢! ∼(φ ➝ ψ) ↔ 𝓢 ⊢! (φ ⋏ ∼ψ) := by
  constructor;
  . intro h; exact (and₁'! ENIpqApNq!) ⨀ h;
  . intro h; exact (and₂'! ENIpqApNq!) ⨀ h;

lemma p_Nq_NIpq! (hp : 𝓢 ⊢! φ) (hnq : 𝓢 ⊢! ∼ψ) : 𝓢 ⊢! ∼(φ ➝ ψ) := by
  apply NIpq_ApNq!.mpr;
  apply and₃'!;
  . exact hp;
  . exact hnq;

end LO.Entailment

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
  apply C!_trans (K!_right neg_equiv!) ?_;
  apply contra!;
  apply CCC!_of_C!_right;
  apply K!_left neg_equiv!;

lemma ONpNq_IpNq! (h : 𝓢 ⊢! ∼φ ⋎ ∼ψ) : 𝓢 ⊢! φ ➝ ∼ψ := by
  apply A!_cases CNC! imply₁! h;

@[simp]
lemma IIIpIqbbApq! : 𝓢 ⊢! ((φ ➝ (ψ ➝ ⊥)) ➝ ⊥) ➝ (φ ⋏ ψ) := by
  apply C!_trans IIIpIqbNIpNq! ?_;
  apply CN!_of_CN!_left
  apply deduct'!;
  have : [∼(φ ⋏ ψ)] ⊢[𝓢]! ∼φ ⋎ ∼ψ := ANN!_of_NK! $ by_axm!
  exact A!_cases CNC! imply₁! this;

lemma IIIpIqbb_Apq! (h : 𝓢 ⊢! ((φ ➝ (ψ ➝ ⊥)) ➝ ⊥)) : 𝓢 ⊢! (φ ⋏ ψ) := IIIpIqbbApq! ⨀ h

lemma Apq_IIpIqbb! (b : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! (φ ➝ ψ ➝ ⊥) ➝ ⊥ := by
  apply deduct'!;
  have h₁ : [φ ➝ ψ ➝ ⊥] ⊢[𝓢]! φ := of'! $ K!_left b;
  have h₂ : [φ ➝ ψ ➝ ⊥] ⊢[𝓢]! ψ := of'! $ K!_right b;
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
  apply K!_intro;
  . apply Iqp_Irs_IIprIqs (K!_right h₁) (K!_left h₂);
  . apply Iqp_Irs_IIprIqs (K!_left h₁) (K!_right h₂);

@[simp]
lemma IIIpbqOpq! : 𝓢 ⊢! ((φ ➝ ⊥) ➝ ψ) ➝ (φ ⋎ ψ) := by
  apply deduct'!;
  apply A!_cases or₁! ?_ lem!;
  . apply deduct!;
    apply A!_intro_right;
    have H₁ : [∼φ, (φ ➝ ⊥) ➝ ψ] ⊢[𝓢]! φ ➝ ⊥ := N!_iff_CO!.mp by_axm!;
    have H₂ : [∼φ, (φ ➝ ⊥) ➝ ψ] ⊢[𝓢]! (φ ➝ ⊥) ➝ ψ := by_axm!;
    exact H₂ ⨀ H₁;

@[simp]
lemma IOpqIIpbq! : 𝓢 ⊢! (φ ⋎ ψ) ➝ ((φ ➝ ⊥) ➝ ψ) := by
  apply deduct'!;
  apply deduct!;
  have : [φ ➝ ⊥, φ ⋎ ψ] ⊢[𝓢]! φ ⋎ ψ := by_axm!;
  apply A!_cases ?_ C!_id this;
  . apply deduct!;
    refine efq! ⨀ ?_;
    have H₁ : [φ, φ ➝ ⊥, φ ⋎ ψ] ⊢[𝓢]! φ := by_axm!;
    have H₂ : [φ, φ ➝ ⊥, φ ⋎ ψ] ⊢[𝓢]! φ ➝ ⊥ := by_axm!;
    exact H₂ ⨀ H₁;

@[simp]
lemma IIIpbqOpq : 𝓢 ⊢! ((φ ➝ ⊥) ➝ ψ) ➝ (φ ⋎ ψ) := by
  apply deduct'!;
  apply A!_cases or₁! ?_ lem!;
  . apply deduct!;
    apply A!_intro_right;
    have H₁ : [∼φ, (φ ➝ ⊥) ➝ ψ] ⊢[𝓢]! φ ➝ ⊥ := N!_iff_CO!.mp by_axm!;
    have H₂ : [∼φ, (φ ➝ ⊥) ➝ ψ] ⊢[𝓢]! (φ ➝ ⊥) ➝ ψ := by_axm!;
    exact H₂ ⨀ H₁;

@[simp]
lemma IOpqIIpbq : 𝓢 ⊢! (φ ⋎ ψ) ➝ ((φ ➝ ⊥) ➝ ψ) := by
  apply deduct'!;
  apply deduct!;
  have : [φ ➝ ⊥, φ ⋎ ψ] ⊢[𝓢]! φ ⋎ ψ := by_axm!;
  apply A!_cases ?_ C!_id this;
  . apply deduct!;
    refine efq! ⨀ ?_;
    have H₁ : [φ, φ ➝ ⊥, φ ⋎ ψ] ⊢[𝓢]! φ := by_axm!;
    have H₂ : [φ, φ ➝ ⊥, φ ⋎ ψ] ⊢[𝓢]! φ ➝ ⊥ := by_axm!;
    exact H₂ ⨀ H₁;

lemma ENIpqApNq! : 𝓢 ⊢! ∼(φ ➝ ψ) ⭤ (φ ⋏ ∼ψ) := by
  apply K!_intro;
  . apply deduct'!;
    apply K!_intro;
    . apply deductInv'!;
      apply CN!_of_CN!_left;
      exact CNC!
    . apply deductInv'!;
      apply CN!_of_CN!_left;
      apply C!_swap;
      apply deduct'!;
      exact dne!;
  . apply not_imply_prem''! and₁! and₂!;

lemma NIpq_ApNq! : 𝓢 ⊢! ∼(φ ➝ ψ) ↔ 𝓢 ⊢! (φ ⋏ ∼ψ) := by
  constructor;
  . intro h; exact (K!_left ENIpqApNq!) ⨀ h;
  . intro h; exact (K!_right ENIpqApNq!) ⨀ h;

lemma p_Nq_NIpq! (hp : 𝓢 ⊢! φ) (hnq : 𝓢 ⊢! ∼ψ) : 𝓢 ⊢! ∼(φ ➝ ψ) := by
  apply NIpq_ApNq!.mpr;
  apply K!_intro;
  . exact hp;
  . exact hnq;

end LO.Entailment

import Foundation.Incompleteness.Arith.DC
import Foundation.Incompleteness.DC.Basic
import Foundation.Modal.Logic.WellKnown

namespace LO.Entailment

open Entailment
open FiniteContext

variable {F : Type*} [LogicalConnective F] [DecidableEq F]
         {S : Type*} [Entailment F S]
         {𝓢 : S} [Entailment.Cl 𝓢]
         {φ ψ χ ξ δ : F}

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

end LO.Entailment



namespace LO

open Entailment FiniteContext
open FirstOrder LO.FirstOrder.DerivabilityCondition
open Modal Modal.Hilbert

variable {L : Language} [Semiterm.Operator.GoedelNumber L (Sentence L)]
         {T₀ T : Theory L}

namespace ProvabilityLogic

/-- Mapping modal prop vars to first-order sentence -/
def Realization (L) := ℕ → FirstOrder.Sentence L

namespace Realization

/-- Mapping modal formulae to first-order sentence -/
def interpret
  (f : Realization L) (𝔅 : ProvabilityPredicate T₀ T) : Formula ℕ → FirstOrder.Sentence L
  | .atom a => f a
  | □φ => 𝔅 (f.interpret 𝔅 φ)
  | ⊥ => ⊥
  | φ ➝ ψ => (f.interpret 𝔅 φ) ➝ (f.interpret 𝔅 ψ)


section

variable {𝔅 : ProvabilityPredicate T₀ T} {f : Realization L} {A B : Modal.Formula _}

lemma iff_interpret_atom : T ⊢!. f.interpret 𝔅 (.atom a) ↔ T ⊢!. f a := by  simp [Realization.interpret];
lemma iff_interpret_imp : T ⊢!. f.interpret 𝔅 (A ➝ B) ↔ T ⊢!. (f.interpret 𝔅 A) ➝ (f.interpret 𝔅 B) := by simp [Realization.interpret];
lemma iff_interpret_bot : T ⊢!. f.interpret 𝔅 ⊥ ↔ T ⊢!. ⊥ := by simp [Realization.interpret];
lemma iff_interpret_box : T ⊢!. f.interpret 𝔅 (□A) ↔ T ⊢!. 𝔅 (f.interpret 𝔅 A) := by simp [Realization.interpret];
lemma iff_interpret_neg : T ⊢!. f.interpret 𝔅 (∼A) ↔ T ⊢!. ∼(f.interpret 𝔅 A) := by
  dsimp [Realization.interpret];
  apply neg_equiv'!.symm;

lemma iff_interpret_neg_inside : T ⊢!. f.interpret 𝔅 (∼A) ⭤ ∼(f.interpret 𝔅 A) := by
  dsimp [Realization.interpret];
  apply and₃'!;
  . apply and₂'! $ neg_equiv!
  . apply and₁'! $ neg_equiv!

variable [DecidableEq (Sentence L)]

lemma iff_interpret_or_inside : T ⊢!. f.interpret 𝔅 (A ⋎ B) ⭤ (f.interpret 𝔅 A) ⋎ (f.interpret 𝔅 B) := by
  apply and₃'!;
  . apply IIIpbqOpq!;
  . apply IOpqIIpbq!;

lemma iff_interpret_or : T ⊢!. f.interpret 𝔅 (A ⋎ B) ↔ T ⊢!. (f.interpret 𝔅 A) ⋎ (f.interpret 𝔅 B) := by
  constructor;
  . intro h; apply (and₁'! iff_interpret_or_inside) ⨀ h;
  . intro h; apply (and₂'! iff_interpret_or_inside) ⨀ h;

lemma iff_interpret_and : T ⊢!. f.interpret 𝔅 (A ⋏ B) ↔ T ⊢!. (f.interpret 𝔅 A) ⋏ (f.interpret 𝔅 B) := by
  constructor;
  . intro h; apply IIIpIqbb_Apq! h;
  . intro h; apply Apq_IIpIqbb! h;

lemma iff_interpret_and_inside : T ⊢!. f.interpret 𝔅 (A ⋏ B) ⭤ (f.interpret 𝔅 A) ⋏ (f.interpret 𝔅 B) := by
  apply and₃'!;
  . apply IIIpIqbbApq!;
  . apply ApqIIpIqbb!;

lemma iff_interpret_and' : T ⊢!. f.interpret 𝔅 (A ⋏ B) ↔ T ⊢!. (f.interpret 𝔅 A) ∧ T ⊢!. (f.interpret 𝔅 B) := by
  apply Iff.trans iff_interpret_and;
  constructor;
  . intro h;
    constructor;
    . apply and₁'! h;
    . apply and₂'! h;
  . rintro ⟨_, _⟩;
    apply and₃'! <;> assumption;

end


lemma letterless_interpret
  {f₁ f₂ : Realization L} (A_letterless : A.letterless)
  : (f₁.interpret 𝔅 A) = (f₂.interpret 𝔅 A) := by
  induction A using Formula.rec' with
  | hatom a => simp at A_letterless;
  | hfalsum => simp_all [Realization.interpret];
  | himp A B ihA ihB =>
    replace ihA := ihA $ Modal.Formula.letterless.def_imp₁ A_letterless;
    replace ihB := ihB $ Modal.Formula.letterless.def_imp₂ A_letterless;
    simp_all [Realization.interpret];
  | hbox A ihA =>
    replace ihA := ihA $ Modal.Formula.letterless.def_box A_letterless;
    simp_all [Realization.interpret];


end Realization

end LO.ProvabilityLogic

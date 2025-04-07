import Foundation.ProvabilityLogic.GL.Completeness
import Foundation.Modal.Boxdot.GL_Grz

namespace LO


namespace Entailment

open Entailment
open FiniteContext

variable {F : Type*} [LogicalConnective F] [DecidableEq F]
         {S : Type*} [Entailment F S]
         {𝓢 : S} [Entailment.Cl 𝓢]
         {φ ψ χ ξ : F}

lemma IIIpIqbNIpNq : 𝓢 ⊢! ((φ ➝ ψ ➝ ⊥) ➝ ⊥) ➝ ∼(φ ➝ ∼ψ) := by
  apply imp_trans''! (and₂'! neg_equiv!) ?_;
  apply contra₀'!;
  apply dhyp_imp'!;
  apply and₁'! neg_equiv!;

lemma ONpNq_IpNq (h : 𝓢 ⊢! ∼φ ⋎ ∼ψ) : 𝓢 ⊢! φ ➝ ∼ψ := by
  apply or₃'''! efq_imply_not₁! imply₁! h;

@[simp]
lemma IIIpIqbbApq : 𝓢 ⊢! ((φ ➝ (ψ ➝ ⊥)) ➝ ⊥) ➝ (φ ⋏ ψ) := by
  apply imp_trans''! IIIpIqbNIpNq ?_;
  apply contra₂'!
  apply deduct'!;
  have : [∼(φ ⋏ ψ)] ⊢[𝓢]! ∼φ ⋎ ∼ψ := demorgan₄'! $ by_axm!
  exact or₃'''! efq_imply_not₁! imply₁! this;

lemma Apq_IIpIqbb (b : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! (φ ➝ ψ ➝ ⊥) ➝ ⊥ := by
  apply deduct'!;
  have h₁ : [φ ➝ ψ ➝ ⊥] ⊢[𝓢]! φ := of'! $ and₁'! b;
  have h₂ : [φ ➝ ψ ➝ ⊥] ⊢[𝓢]! ψ := of'! $ and₂'! b;
  have H : [φ ➝ ψ ➝ ⊥] ⊢[𝓢]! φ ➝ ψ ➝ ⊥ := by_axm!;
  exact (H ⨀ h₁) ⨀ h₂;

@[simp]
lemma ApqIIpIqbb : 𝓢 ⊢! (φ ⋏ ψ) ➝ ((φ ➝ ψ ➝ ⊥) ➝ ⊥) := by
  apply deduct'!;
  apply Apq_IIpIqbb;
  apply by_axm!;
  simp;

lemma Epq_Ers_EEw (h₁ : 𝓢 ⊢! ψ ➝ φ) (h₂ : 𝓢 ⊢! χ ➝ ξ) : 𝓢 ⊢! (φ ➝ χ) ➝ (ψ ➝ ξ) := by
  replace h₁ : [ψ, φ ➝ χ] ⊢[𝓢]! ψ ➝ φ := of'! $ h₁;
  replace h₂ : [ψ, φ ➝ χ] ⊢[𝓢]! χ ➝ ξ := of'! $ h₂;
  have h₃ : [ψ, φ ➝ χ] ⊢[𝓢]! φ ➝ χ := by_axm!;
  apply deduct'!;
  apply deduct!;
  exact h₂ ⨀ (h₃ ⨀ (h₁ ⨀ (by_axm!)))

lemma Epq_Ers_EE (h₁ : 𝓢 ⊢! φ ⭤ ψ) (h₂ : 𝓢 ⊢! χ ⭤ ξ) : 𝓢 ⊢! (φ ➝ χ) ⭤ (ψ ➝ ξ) := by
  apply and₃'!;
  . apply Epq_Ers_EEw (and₂'! h₁) (and₁'! h₂);
  . apply Epq_Ers_EEw (and₁'! h₁) (and₂'! h₂);

end Entailment


open FirstOrder FirstOrder.DerivabilityCondition
open Modal
open Modal.Hilbert
open FirstOrder
open Entailment FiniteContext

namespace ProvabilityLogic

variable {L} [Semiterm.Operator.GoedelNumber L (Sentence L)] [DecidableEq (Sentence L)]
         {T₀ T : Theory L} [T₀ ⪯ T] {A : Modal.Formula ℕ}

namespace Realization

variable {𝔅 : ProvabilityPredicate T₀ T} {f : Realization L} {A B : Modal.Formula _}

private def strong_interpretAux
  {T U : FirstOrder.Theory L}
  (f : Realization L) (𝔅 : ProvabilityPredicate T U) : Formula ℕ → Sentence L
  | .atom a => f a
  | ⊥ => ⊥
  | φ ➝ ψ => (f.strong_interpretAux 𝔅 φ) ➝ (f.strong_interpretAux 𝔅 ψ)
  | □φ => ((f.strong_interpretAux 𝔅 φ) ➝ 𝔅 (f.strong_interpretAux 𝔅 φ) ➝ ⊥) ➝ ⊥

omit [DecidableEq (Sentence L)] [T₀ ⪯ T] in
private lemma eq_boxdotTranslated_strong_interpretAux : f.interpret 𝔅 (Aᵇ) = f.strong_interpretAux 𝔅 A := by
  induction A using Formula.rec' <;> simp_all [Formula.BoxdotTranslation, Realization.interpret, strong_interpretAux];

def strong_interpret (f : Realization L) (𝔅 : ProvabilityPredicate T₀ T) : Formula ℕ → Sentence L
  | .atom a => f a
  | ⊥ => ⊥
  | φ ➝ ψ => (f.strong_interpret 𝔅 φ) ➝ (f.strong_interpret 𝔅 ψ)
  | □φ => (f.strong_interpret 𝔅 φ) ⋏ 𝔅 (f.strong_interpret 𝔅 φ)

private lemma iff_strong_interpret_strong_interpretAux' [𝔅.HBL2] :
  T ⊢!. f.strong_interpretAux 𝔅 A ⭤ f.strong_interpret 𝔅 A:= by
  induction A using Formula.rec' with
  | hatom φ => simp [strong_interpret, strong_interpretAux];
  | hfalsum => simp [strong_interpret, strong_interpretAux];
  | himp A B ihA ihB => exact Epq_Ers_EE ihA ihB;
  | hbox A ihA =>
    simp [strong_interpret, strong_interpretAux];
    generalize f.strong_interpretAux 𝔅 A = φ at ihA ⊢;
    generalize f.strong_interpret 𝔅 A = ψ at ihA ⊢;
    apply and₃'!;
    . apply imp_trans''! ?_ IIIpIqbbApq;
      apply rev_dhyp_imp'!;
      apply deduct'!;
      apply deduct!;
      apply deduct!;
      replace : [𝔅 φ, φ, ψ ➝ (𝔅 ψ) ➝ ⊥] ⊢[T.alt]! (𝔅 φ ➝ 𝔅 ψ) := and₁'! $ of'! $ WeakerThan.pbl $ 𝔅.prov_distribute_iff ihA;
      replace ihA : [𝔅 φ, φ, ψ ➝ (𝔅 ψ) ➝ ⊥] ⊢[T.alt]! φ ➝ ψ := of'! $ and₁'! ihA;
      have H₁ : [𝔅 φ, φ, ψ ➝ (𝔅 ψ) ➝ ⊥] ⊢[T.alt]! φ := by_axm!;
      have H₂ : [𝔅 φ, φ, ψ ➝ (𝔅 ψ) ➝ ⊥] ⊢[T.alt]! ψ ➝ (𝔅 ψ) ➝ ⊥ := by_axm!;
      have H₃ : [𝔅 φ, φ, ψ ➝ (𝔅 ψ) ➝ ⊥] ⊢[T.alt]! 𝔅 φ := by_axm!;
      exact (H₂ ⨀ (ihA ⨀ H₁)) ⨀ (this ⨀ H₃);
    . apply imp_trans''! ApqIIpIqbb ?_;
      apply rev_dhyp_imp'!;
      apply deduct'!;
      apply deduct!;
      apply deduct!;
      replace : [𝔅 ψ, ψ, φ ➝ 𝔅 φ ➝ ⊥] ⊢[T.alt]! (𝔅 ψ ➝ 𝔅 φ) := and₂'! $ of'! $ WeakerThan.pbl $ 𝔅.prov_distribute_iff ihA;
      replace ihA : [𝔅 ψ, ψ, φ ➝ 𝔅 φ ➝ ⊥] ⊢[T.alt]! ψ ➝ φ := of'! $ and₂'! ihA;
      have H₁ : [𝔅 ψ, ψ, φ ➝ 𝔅 φ ➝ ⊥] ⊢[T.alt]! ψ := by_axm!;
      have H₂ : [𝔅 ψ, ψ, φ ➝ 𝔅 φ ➝ ⊥] ⊢[T.alt]! φ ➝ 𝔅 φ ➝ ⊥ := by_axm!;
      have H₃ : [𝔅 ψ, ψ, φ ➝ 𝔅 φ ➝ ⊥] ⊢[T.alt]! 𝔅 ψ := by_axm!;
      exact (H₂ ⨀ (ihA ⨀ H₁)) ⨀ (this ⨀ H₃);

private lemma iff_strong_interpret_strong_interpretAux [𝔅.HBL2] :
  T ⊢!. f.strong_interpretAux 𝔅 A ↔ T ⊢!. f.strong_interpret 𝔅 A:= by
  constructor;
  . intro h; apply (and₁'! iff_strong_interpret_strong_interpretAux') ⨀ h;
  . intro h; apply (and₂'! iff_strong_interpret_strong_interpretAux') ⨀ h;

lemma iff_strong_interpret [𝔅.HBL2] : T ⊢!. f.interpret 𝔅 (Aᵇ) ↔ T ⊢!. f.strong_interpret 𝔅 A := by
  rw [eq_boxdotTranslated_strong_interpretAux];
  exact iff_strong_interpret_strong_interpretAux;

end Realization

theorem arithmetical_completeness_Grz_iff {T : Theory ℒₒᵣ} [T.Delta1Definable] [𝐈𝚺₁ ⪯ T] [Arith.SoundOn T (Arith.Hierarchy 𝚷 2)] :
  (∀ {f : Realization ℒₒᵣ}, T ⊢!. f.strong_interpret ((𝐈𝚺₁).standardDP T) A) ↔ A ∈ Logic.Grz := by
  constructor;
  . intro h;
    suffices Aᵇ ∈ Logic.GL by exact BoxdotProperty.bdp.mp this;
    apply arithmetical_completeness_GL_iff (T := T).mp;
    intro f;
    apply Realization.iff_strong_interpret (L := ℒₒᵣ).mpr;
    apply h;
  . intro h f;
    replace h : Aᵇ ∈ Logic.GL := BoxdotProperty.bdp.mpr h;
    have : (∀ {f : Realization ℒₒᵣ}, T ⊢!. f.interpret ((𝐈𝚺₁).standardDP T) (Aᵇ)) := arithmetical_completeness_GL_iff.mpr h;
    exact Realization.iff_strong_interpret (L := ℒₒᵣ) |>.mp $ this;

end LO.ProvabilityLogic

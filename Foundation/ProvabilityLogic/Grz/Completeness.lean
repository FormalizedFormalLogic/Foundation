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

def strongInterpret (f : Realization L) (𝔅 : ProvabilityPredicate T₀ T) : Formula ℕ → Sentence L
  | .atom a => f a
  | ⊥ => ⊥
  | φ ➝ ψ => (f.strongInterpret 𝔅 φ) ➝ (f.strongInterpret 𝔅 ψ)
  | □φ => (f.strongInterpret 𝔅 φ) ⋏ 𝔅 (f.strongInterpret 𝔅 φ)

lemma iff_interpret_boxdot_strongInterpret_inside [𝔅.HBL2] : T ⊢!. f.interpret 𝔅 (Aᵇ) ⭤ f.strongInterpret 𝔅 A := by
  induction A using Formula.rec' with
  | hatom φ => simp [Realization.interpret, strongInterpret, Formula.BoxdotTranslation];
  | hfalsum => simp [Realization.interpret, strongInterpret, Formula.BoxdotTranslation];
  | himp A B ihA ihB => exact Epq_Ers_EIprIqs! ihA ihB;
  | hbox A ih =>
    apply and₃'!;
    . apply imp_trans''! IIIpIqbbApq! ?_;
      apply and_replace!;
      . exact and₁'! ih;
      . exact 𝔅.prov_distribute_imply'' $ and₁'! ih;
    . apply imp_trans''! ?_ ApqIIpIqbb!;
      apply and_replace!;
      . exact and₂'! ih;
      . exact 𝔅.prov_distribute_imply'' $ and₂'! ih;

lemma iff_interpret_boxdot_strongInterpret [𝔅.HBL2] : T ⊢!. f.interpret 𝔅 (Aᵇ) ↔ T ⊢!. f.strongInterpret 𝔅 A := by
  constructor;
  . intro h; exact (and₁'! iff_interpret_boxdot_strongInterpret_inside) ⨀ h;
  . intro h; exact (and₂'! iff_interpret_boxdot_strongInterpret_inside) ⨀ h;

end Realization

theorem Grz.arithmetical_completeness_iff {T : Theory ℒₒᵣ} [T.Delta1Definable] [𝐈𝚺₁ ⪯ T] [Arith.SoundOn T (Arith.Hierarchy 𝚷 2)] :
  (∀ {f : Realization ℒₒᵣ}, T ⊢!. f.strongInterpret ((𝐈𝚺₁).standardDP T) A) ↔ A ∈ Logic.Grz := by
  constructor;
  . intro h;
    suffices Aᵇ ∈ Logic.GL by exact BoxdotProperty.bdp.mp this;
    apply GL.arithmetical_completeness_iff (T := T).mp;
    intro f;
    apply Realization.iff_interpret_boxdot_strongInterpret (L := ℒₒᵣ).mpr;
    apply h;
  . intro h f;
    replace h : Aᵇ ∈ Logic.GL := BoxdotProperty.bdp.mpr h;
    have : (∀ {f : Realization ℒₒᵣ}, T ⊢!. f.interpret ((𝐈𝚺₁).standardDP T) (Aᵇ)) := GL.arithmetical_completeness_iff.mpr h;
    exact Realization.iff_interpret_boxdot_strongInterpret (L := ℒₒᵣ) |>.mp $ this;

end LO.ProvabilityLogic

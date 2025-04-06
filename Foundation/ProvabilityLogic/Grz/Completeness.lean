import Foundation.ProvabilityLogic.GL.Completeness
import Foundation.Modal.Boxdot.GL_Grz

namespace LO


namespace Entailment

open Entailment
open FiniteContext

variable {F : Type*} [LogicalConnective F] [DecidableEq F]
         {S : Type*} [Entailment F S]
         {𝓢 : S} [Entailment.Classical 𝓢]
         {φ ψ ξ : F}

lemma IIIpIqbNIpNq : 𝓢 ⊢! ((φ ➝ ψ ➝ ⊥) ➝ ⊥) ➝ ∼(φ ➝ ∼ψ) := by
  apply imp_trans''! (and₂'! neg_equiv!) ?_;
  apply contra₀'!;
  apply dhyp_imp'!;
  apply and₁'! neg_equiv!;

lemma ONpNq_IpNq (h : 𝓢 ⊢! ∼φ ⋎ ∼ψ) : 𝓢 ⊢! φ ➝ ∼ψ := by
  apply or₃'''! efq_imply_not₁! imply₁! h;

lemma IIIpIqbbApq : 𝓢 ⊢! ((φ ➝ (ψ ➝ ⊥)) ➝ ⊥) ➝ (φ ⋏ ψ) := by
  apply imp_trans''! IIIpIqbNIpNq ?_;
  apply contra₂'!
  apply deduct'!;
  have : [∼(φ ⋏ ψ)] ⊢[𝓢]! ∼φ ⋎ ∼ψ := demorgan₄'! $ by_axm!
  exact or₃'''! efq_imply_not₁! imply₁! this;

lemma IIpIqbb_Apq (b : 𝓢 ⊢! (φ ➝ (ψ ➝ ⊥)) ➝ ⊥) : 𝓢 ⊢! φ ⋏ ψ := IIIpIqbbApq ⨀ b

lemma Apq_IIpIqbb (b : 𝓢 ⊢! φ ⋏ ψ) : 𝓢 ⊢! (φ ➝ ψ ➝ ⊥) ➝ ⊥ := by
  apply deduct'!;
  have h₁ : [φ ➝ ψ ➝ ⊥] ⊢[𝓢]! φ := of'! $ and₁'! b;
  have h₂ : [φ ➝ ψ ➝ ⊥] ⊢[𝓢]! ψ := of'! $ and₂'! b;
  have H : [φ ➝ ψ ➝ ⊥] ⊢[𝓢]! φ ➝ ψ ➝ ⊥ := by_axm!;
  exact (H ⨀ h₁) ⨀ h₂;

end Entailment


open FirstOrder FirstOrder.DerivabilityCondition
open Modal
open Modal.Hilbert
open FirstOrder
open Entailment

namespace ProvabilityLogic

variable {L} [Semiterm.Operator.GoedelNumber L (Sentence L)] [DecidableEq (Sentence L)]
         {T₀ T U : Theory L} {A : Modal.Formula ℕ}

namespace Realization

variable {𝔅 : ProvabilityPredicate T₀ T} {f : Realization L} {A B : Modal.Formula _}

private def strong_interpretAux
  {T U : FirstOrder.Theory L}
  (f : Realization L) (𝔅 : ProvabilityPredicate T U) : Formula ℕ → Sentence L
  | .atom a => f a
  | ⊥ => ⊥
  | φ ➝ ψ => (f.strong_interpretAux 𝔅 φ) ➝ (f.strong_interpretAux 𝔅 ψ)
  | □φ => ((f.strong_interpretAux 𝔅 φ) ➝ 𝔅 (f.strong_interpretAux 𝔅 φ) ➝ ⊥) ➝ ⊥

omit [DecidableEq (Sentence L)] in
private lemma eq_boxdotTranslated_strong_interpretAux : f.interpret 𝔅 (Aᵇ) = f.strong_interpretAux 𝔅 A := by
  induction A using Formula.rec' <;> simp_all [Formula.BoxdotTranslation, Realization.interpret, strong_interpretAux];

def strong_interpret (f : Realization L) (𝔅 : ProvabilityPredicate T U) : Formula ℕ → Sentence L
  | .atom a => f a
  | ⊥ => ⊥
  | φ ➝ ψ => (f.strong_interpretAux 𝔅 φ) ➝ (f.strong_interpretAux 𝔅 ψ)
  | □φ => (f.strong_interpretAux 𝔅 φ) ⋏ 𝔅 (f.strong_interpretAux 𝔅 φ)

private lemma iff_strong_interpret_strong_interpretAux :
  U ⊢!. f.strong_interpretAux 𝔅 A ↔ U ⊢!. f.strong_interpret 𝔅 A:= by
  induction A using Formula.rec' with
  | hatom φ => rfl;
  | hfalsum => rfl;
  | himp A B ihA ihB => simp [strong_interpret, strong_interpretAux];
  | hbox A ihA =>
    simp [strong_interpret, strong_interpretAux];
    constructor;
    . intro h; exact IIpIqbb_Apq $ h;
    . intro h; exact Apq_IIpIqbb $ h;

lemma iff_strong_interpret : U ⊢!. f.interpret 𝔅 (Aᵇ) ↔ U ⊢!. f.strong_interpret 𝔅 A := by
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

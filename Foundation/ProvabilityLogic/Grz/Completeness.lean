import Foundation.ProvabilityLogic.GL.Completeness
import Foundation.Modal.Boxdot.GL_Grz

namespace LO.ProvabilityLogic

open FirstOrder FirstOrder.DerivabilityCondition
open Modal
open Modal.Hilbert
open FirstOrder
open Entailment FiniteContext

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
  | himp A B ihA ihB => exact Epq_Ers_EIprIqs! ihA ihB;
  | hbox A ihA =>
    dsimp [strong_interpretAux, strong_interpret];
    generalize f.strong_interpretAux 𝔅 A = φ at ihA ⊢;
    generalize f.strong_interpret 𝔅 A = ψ at ihA ⊢;
    apply and₃'!;
    . apply imp_trans''! ?_ IIIpIqbbApq!;
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
    . apply imp_trans''! ApqIIpIqbb! ?_;
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

theorem Grz.arithmetical_completeness_iff {T : Theory ℒₒᵣ} [T.Delta1Definable] [𝐈𝚺₁ ⪯ T] [Arith.SoundOn T (Arith.Hierarchy 𝚷 2)] :
  (∀ {f : Realization ℒₒᵣ}, T ⊢!. f.strong_interpret ((𝐈𝚺₁).standardDP T) A) ↔ A ∈ Logic.Grz := by
  constructor;
  . intro h;
    suffices Aᵇ ∈ Logic.GL by exact BoxdotProperty.bdp.mp this;
    apply GL.arithmetical_completeness_iff (T := T).mp;
    intro f;
    apply Realization.iff_strong_interpret (L := ℒₒᵣ).mpr;
    apply h;
  . intro h f;
    replace h : Aᵇ ∈ Logic.GL := BoxdotProperty.bdp.mpr h;
    have : (∀ {f : Realization ℒₒᵣ}, T ⊢!. f.interpret ((𝐈𝚺₁).standardDP T) (Aᵇ)) := GL.arithmetical_completeness_iff.mpr h;
    exact Realization.iff_strong_interpret (L := ℒₒᵣ) |>.mp $ this;

end LO.ProvabilityLogic

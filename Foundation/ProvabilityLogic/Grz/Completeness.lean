import Foundation.ProvabilityLogic.GL.Completeness
import Foundation.ProvabilityLogic.S.Completeness
import Foundation.Modal.Boxdot.GL_Grz

namespace LO

open FirstOrder FirstOrder.DerivabilityCondition
open Modal
open Modal.Hilbert
open FirstOrder
open Entailment FiniteContext

namespace FirstOrder

variable {L} {M : Type*} [Nonempty M] [Structure L M]

@[simp] lemma models₀_and_iff (σ π : Sentence L) : M ⊧ₘ₀ (σ ⋏ π) ↔ M ⊧ₘ₀ σ ∧ M ⊧ₘ₀ π := by simp [models₀_iff]

@[simp] lemma models₀_bot_iff : ¬(M ⊧ₘ₀ (⊥ : Sentence L)) := by simp [models₀_iff]

@[simp] lemma models₀_top_iff : M ⊧ₘ₀ (⊤ : Sentence L) := by simp [models₀_iff];

end FirstOrder


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

lemma iff_models_interpret_boxdot_strongInterpret {M} [Nonempty M] [Structure L M] [M ⊧ₘ* T] [𝔅.HBL2] [𝔅.Sound M] : M ⊧ₘ₀ f.interpret 𝔅 (Aᵇ) ↔ M ⊧ₘ₀ f.strongInterpret 𝔅 A := by
  induction A using Formula.rec' with
  | hatom φ => simp [Realization.interpret, strongInterpret, Formula.BoxdotTranslation];
  | hfalsum => simp [Realization.interpret, strongInterpret, Formula.BoxdotTranslation];
  | himp A B ihA ihB =>
    simp only [Formula.BoxdotTranslation, interpret, models₀_imply_iff, strongInterpret];
    constructor;
    . intro hAB hA;
      apply ihB.mp;
      apply hAB;
      apply ihA.mpr;
      exact hA;
    . intro hAB hA;
      apply ihB.mpr;
      apply hAB;
      apply ihA.mp;
      exact hA;
  | hbox A ih =>
    suffices (M ⊧ₘ₀ f.interpret 𝔅 (Aᵇ)) ∧ (M ⊧ₘ₀ 𝔅 (f.interpret 𝔅 (Aᵇ))) ↔ M ⊧ₘ₀ f.strongInterpret 𝔅 A ∧ M ⊧ₘ₀ 𝔅 (f.strongInterpret 𝔅 A) by
      simpa [Formula.BoxdotTranslation, interpret, strongInterpret] using this;
    constructor;
    . rintro ⟨h₁, h₂⟩;
      constructor;
      . exact ih.mp h₁;
      . apply 𝔅.sound (T := T).mpr;
        exact iff_interpret_boxdot_strongInterpret.mp $ 𝔅.sound (T := T).mp h₂;
    . rintro ⟨h₁, h₂⟩;
      constructor;
      . apply ih.mpr h₁;
      . apply 𝔅.sound (T := T).mpr;
        exact iff_interpret_boxdot_strongInterpret.mpr $ 𝔅.sound (T := T).mp h₂;

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


lemma iff_boxdot_GL_S : Aᵇ ∈ Logic.GL ↔ Aᵇ ∈ Logic.S := by
  constructor;
  . apply GL_subset_S;
  . intro h;
    replace h := Modal.Logic.iff_provable_rfl_GL_provable_S.mpr h;
    replace h := Hilbert.GL.Kripke.iff_provable_satisfies_FiniteTransitiveTree.mp h;
    apply Hilbert.GL.Kripke.iff_provable_satisfies_FiniteTransitiveTree.mpr;
    intro M r M_tree;
    let M' := M;
    let w := r;
    have := h M w ?_;
    . sorry;
    . sorry;

theorem Grz.arithmetical_completeness_model_iff
  {T : Theory ℒₒᵣ} [T.Delta1Definable] [𝐈𝚺₁ ⪯ T] [Arith.SoundOn T (Arith.Hierarchy 𝚷 2)] [ℕ ⊧ₘ* T] :
  (∀ {f : Realization ℒₒᵣ}, ℕ ⊧ₘ₀ f.strongInterpret ((𝐈𝚺₁).standardDP T) A) ↔ A ∈ Logic.Grz := by
  apply Iff.trans ?_ iff_boxdotTranslatedGL_Grz;
  apply Iff.trans ?_ iff_boxdot_GL_S.symm;
  apply Iff.trans ?_ (S.arithmetical_completeness_iff (T := T)).symm;
  constructor;
  . intro h f; exact Realization.iff_models_interpret_boxdot_strongInterpret (L := ℒₒᵣ) |>.mpr $ h;
  . intro h f; exact Realization.iff_models_interpret_boxdot_strongInterpret (L := ℒₒᵣ) |>.mp $ h f;

end LO.ProvabilityLogic

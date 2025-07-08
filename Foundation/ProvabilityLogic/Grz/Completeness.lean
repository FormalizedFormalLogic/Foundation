import Foundation.Modal.Boxdot.Grz_S

namespace LO

open FirstOrder
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

lemma iff_interpret_boxdot_strongInterpret_inside [L.DecidableEq] [𝔅.HBL2] :
    T ⊢!. f.interpret 𝔅 (Aᵇ) ⭤ f.strongInterpret 𝔅 A := by
  induction A with
  | hatom φ => simp [Realization.interpret, strongInterpret, Formula.boxdotTranslate];
  | hfalsum => simp [Realization.interpret, strongInterpret, Formula.boxdotTranslate];
  | himp A B ihA ihB => exact ECC!_of_E!_of_E! ihA ihB;
  | hbox A ih =>
    apply K!_intro;
    . apply C!_trans CCCCOOK! ?_;
      apply CKK!_of_C!_of_C!;
      . exact K!_left ih;
      . exact 𝔅.prov_distribute_imply'' $ K!_left ih;
    . apply C!_trans ?_ CKCCCOO!;
      apply CKK!_of_C!_of_C!;
      . exact K!_right ih;
      . exact 𝔅.prov_distribute_imply'' $ K!_right ih;

lemma iff_interpret_boxdot_strongInterpret [L.DecidableEq] [𝔅.HBL2] :
    T ⊢!. f.interpret 𝔅 (Aᵇ) ↔ T ⊢!. f.strongInterpret 𝔅 A := by
  constructor;
  . intro h; exact (K!_left iff_interpret_boxdot_strongInterpret_inside) ⨀ h;
  . intro h; exact (K!_right iff_interpret_boxdot_strongInterpret_inside) ⨀ h;

lemma iff_models_interpret_boxdot_strongInterpret
    [L.DecidableEq] {M} [Nonempty M] [Structure L M] [M ⊧ₘ* T] [𝔅.HBL2] [𝔅.Sound M] :
    M ⊧ₘ₀ f.interpret 𝔅 (Aᵇ) ↔ M ⊧ₘ₀ f.strongInterpret 𝔅 A := by
  induction A with
  | hatom φ => simp [Realization.interpret, strongInterpret, Formula.boxdotTranslate];
  | hfalsum => simp [Realization.interpret, strongInterpret, Formula.boxdotTranslate];
  | himp A B ihA ihB =>
    simp only [Formula.boxdotTranslate, interpret, models₀_imply_iff, strongInterpret];
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
      simpa [Formula.boxdotTranslate, interpret, strongInterpret] using this;
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

theorem Grz.arithmetical_completeness_iff {T : ArithmeticTheory} [T.Delta1Definable] [𝐈𝚺₁ ⪯ T] [T.SoundOn (Arithmetic.Hierarchy 𝚷 2)] :
    (∀ {f : Realization ℒₒᵣ}, T ⊢!. f.strongInterpret T.standardPr A) ↔ Modal.Grz ⊢! A := by
  constructor;
  . intro h;
    suffices Modal.GL ⊢! Aᵇ by apply iff_boxdot_GL_Grz.mp this;
    apply GL.arithmetical_completeness_iff (T := T).mp;
    intro f;
    apply Realization.iff_interpret_boxdot_strongInterpret (L := ℒₒᵣ).mpr;
    apply h;
  . intro h f;
    replace h := iff_boxdot_GL_Grz.mpr h;
    have : (∀ {f : Realization ℒₒᵣ}, T ⊢!. f.interpret T.standardPr (Aᵇ)) := GL.arithmetical_completeness_iff.mpr h;
    exact Realization.iff_interpret_boxdot_strongInterpret (L := ℒₒᵣ) |>.mp $ this;

theorem Grz.arithmetical_completeness_model_iff
    {T : ArithmeticTheory} [T.Delta1Definable] [𝐈𝚺₁ ⪯ T] [ℕ ⊧ₘ* T] :
    (∀ {f : Realization ℒₒᵣ}, ℕ ⊧ₘ₀ f.strongInterpret T.standardPr A) ↔ Modal.Grz ⊢! A := by
  apply Iff.trans ?_ Modal.Logic.iff_provable_Grz_provable_boxdot_S;
  apply Iff.trans ?_ (S.arithmetical_completeness_iff (T := T)).symm;
  have : 𝐑₀ ⪯ T := WeakerThan.trans (inferInstanceAs (𝐑₀ ⪯ 𝐈𝚺₁)) inferInstance
  constructor;
  . intro h f; exact Realization.iff_models_interpret_boxdot_strongInterpret (L := ℒₒᵣ) |>.mpr $ h;
  . intro h f; exact Realization.iff_models_interpret_boxdot_strongInterpret (L := ℒₒᵣ) |>.mp $ h f;

end LO.ProvabilityLogic

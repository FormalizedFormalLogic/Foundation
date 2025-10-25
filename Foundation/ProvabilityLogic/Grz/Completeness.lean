import Foundation.Modal.Boxdot.Grz_S

namespace LO

open FirstOrder
open Modal
open Modal.Hilbert
open FirstOrder
open Entailment FiniteContext

namespace ProvabilityLogic

variable {L : Language} [L.ReferenceableBy L] [L.DecidableEq]
         {T₀ T : Theory L} [T₀ ⪯ T] {A : Modal.Formula ℕ}

namespace Realization

variable {𝔅 : Provability T₀ T} {f : Realization 𝔅} {A B : Modal.Formula _}

def strongInterpret (f : Realization 𝔅) : Formula ℕ → Sentence L
  | .atom a => f a
  | ⊥ => ⊥
  | φ ➝ ψ => (f.strongInterpret φ) ➝ (f.strongInterpret ψ)
  | □φ => (f.strongInterpret φ) ⋏ 𝔅 (f.strongInterpret φ)

lemma iff_interpret_boxdot_strongInterpret_inside [𝔅.HBL2] :
    T ⊢ f (Aᵇ) ⭤ f.strongInterpret A := by
  induction A with
  | hatom φ => simp [Realization.interpret, strongInterpret, Formula.boxdotTranslate];
  | hfalsum => simp [strongInterpret, Formula.boxdotTranslate];
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

lemma iff_interpret_boxdot_strongInterpret [𝔅.HBL2] :
    T ⊢ f (Aᵇ) ↔ T ⊢ f.strongInterpret A := by
  constructor;
  . intro h; exact (K!_left iff_interpret_boxdot_strongInterpret_inside) ⨀ h;
  . intro h; exact (K!_right iff_interpret_boxdot_strongInterpret_inside) ⨀ h;

lemma iff_models_interpret_boxdot_strongInterpret
    {M} [Nonempty M] [Structure L M] [M ⊧ₘ* T] [𝔅.HBL2] [𝔅.SoundOnModel M] :
    M ⊧ₘ f (Aᵇ) ↔ M ⊧ₘ f.strongInterpret A := by
  induction A with
  | hatom φ => simp [Realization.interpret, strongInterpret, Formula.boxdotTranslate];
  | hfalsum => simp [strongInterpret, Formula.boxdotTranslate];
  | himp A B ihA ihB =>
    simp only [Formula.boxdotTranslate, interpret, Models, Semantics.Imp.models_imply, strongInterpret];
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
    suffices (M ⊧ₘ f (Aᵇ)) ∧ (M ⊧ₘ 𝔅 (f (Aᵇ))) ↔ M ⊧ₘ f.strongInterpret A ∧ M ⊧ₘ 𝔅 (f.strongInterpret A) by
      simpa [Formula.boxdotTranslate, interpret, strongInterpret] using this;
    constructor;
    . rintro ⟨h₁, h₂⟩;
      constructor;
      . exact ih.mp h₁;
      . apply Provability.SoundOnModel.sound.mpr;
        exact iff_interpret_boxdot_strongInterpret.mp $ Provability.SoundOnModel.sound.mp h₂;
    . rintro ⟨h₁, h₂⟩;
      constructor;
      . apply ih.mpr h₁;
      . apply Provability.SoundOnModel.sound.mpr;
        exact iff_interpret_boxdot_strongInterpret.mpr $ Provability.SoundOnModel.sound.mp h₂;

end Realization

theorem Grz.arithmetical_completeness_iff
    {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] (height : T.standardProvability.height = ⊤) :
    (∀ f : T.StandardRealization, T ⊢ f.strongInterpret A) ↔ Modal.Grz ⊢ A := by
  constructor;
  . intro h;
    suffices Modal.GL ⊢ Aᵇ by apply iff_boxdot_GL_Grz.mp this;
    apply GL.arithmetical_completeness_iff height |>.mp;
    intro f;
    apply Realization.iff_interpret_boxdot_strongInterpret (L := ℒₒᵣ).mpr;
    apply h;
  . intro h f;
    replace h := iff_boxdot_GL_Grz.mpr h;
    have : (∀ f : T.StandardRealization, T ⊢ f (Aᵇ)) := GL.arithmetical_completeness_iff height |>.mpr h;
    exact Realization.iff_interpret_boxdot_strongInterpret (L := ℒₒᵣ) |>.mp $ this f;

theorem Grz.arithmetical_completeness_model_iff
    {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [ℕ ⊧ₘ* T] :
    (∀ f : T.StandardRealization, ℕ ⊧ₘ f.strongInterpret A) ↔ Modal.Grz ⊢ A := by
  apply Iff.trans ?_ Modal.Logic.iff_provable_Grz_provable_boxdot_S;
  apply Iff.trans ?_ (S.arithmetical_completeness_iff (T := T)).symm;
  have : 𝗥₀ ⪯ T := WeakerThan.trans (inferInstanceAs (𝗥₀ ⪯ 𝗜𝚺₁)) inferInstance
  constructor;
  . intro h f; exact Realization.iff_models_interpret_boxdot_strongInterpret (L := ℒₒᵣ) |>.mpr $ h f;
  . intro h f; exact Realization.iff_models_interpret_boxdot_strongInterpret (L := ℒₒᵣ) |>.mp $ h f;

end LO.ProvabilityLogic

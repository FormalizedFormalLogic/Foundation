module

public import Foundation.Modal.Boxdot.Grz_S

@[expose] public section
namespace LO

open FirstOrder
open Modal
open Modal.Hilbert
open FirstOrder FirstOrder.ProvabilityAbstraction
open Entailment FiniteContext
open Provability

namespace Entailment


variable {F : Type*} [LogicalConnective F] [DecidableEq F]
         {S : Type*} [Entailment S F]
         {𝓢 : S} [Entailment.Cl 𝓢]
         {φ ψ χ ξ : F}

lemma CCCCOOK! : 𝓢 ⊢ ((φ ➝ (ψ ➝ ⊥)) ➝ ⊥) ➝ (φ ⋏ ψ) := by cl_prover

lemma CKCCCOO! : 𝓢 ⊢ (φ ⋏ ψ) ➝ ((φ ➝ ψ ➝ ⊥) ➝ ⊥) := by cl_prover;

end Entailment



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

lemma iff_interpret_boxdot_strongInterpret_inside [𝔅.HBL2] : T ⊢ f (Aᵇ) ⭤ f.strongInterpret A := by
  induction A with
  | hatom φ => simp [Realization.interpret, strongInterpret, Formula.boxdotTranslate];
  | hfalsum => simp [strongInterpret, Formula.boxdotTranslate];
  | himp A B ihA ihB => exact ECC!_of_E!_of_E! ihA ihB;
  | hbox A ih =>
    apply E!_trans Realization.interpret.iff_provable_boxdot_inside;
    apply K!_intro;
    . apply CKK!_of_C!_of_C!;
      . cl_prover [ih];
      . apply prov_distribute_imply'';
        cl_prover [ih];
    . apply CKK!_of_C!_of_C!;
      . cl_prover [ih];
      . apply prov_distribute_imply'';
        cl_prover [ih];

lemma iff_interpret_boxdot_strongInterpret [𝔅.HBL2] :
    T ⊢ f (Aᵇ) ↔ T ⊢ f.strongInterpret A := by
  constructor;
  . intro h; exact (K!_left iff_interpret_boxdot_strongInterpret_inside) ⨀ h;
  . intro h; exact (K!_right iff_interpret_boxdot_strongInterpret_inside) ⨀ h;

lemma iff_models_interpret_boxdot_strongInterpret
  {M} [Nonempty M] [Structure L M] [M ⊧ₘ* T] [𝔅.HBL2] [∀ σ, 𝔅.SoundOn M σ] :
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
      . apply models_of_provable (T := T) inferInstance;
        apply ProvabilityAbstraction.D1_shift;
        exact iff_interpret_boxdot_strongInterpret.mp $ 𝔅.sound_on h₂;
    . rintro ⟨h₁, h₂⟩;
      constructor;
      . apply ih.mpr h₁;
      . apply models_of_provable (T := T) inferInstance;
        apply ProvabilityAbstraction.D1_shift;
        exact iff_interpret_boxdot_strongInterpret.mpr $ 𝔅.sound_on h₂;

end Realization

theorem Grz.arithmetical_completeness_iff
    {T : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] (height : T.height = ⊤)
    : (∀ f : T.StandardRealization, T ⊢ f.strongInterpret A) ↔ Modal.Grz ⊢ A := by
  constructor;
  . intro h;
    suffices Modal.GL ⊢ Aᵇ by apply iff_provable_boxdot_GL_provable_Grz.mp this;
    apply GL.arithmetical_completeness_iff height |>.mp;
    intro f;
    apply Realization.iff_interpret_boxdot_strongInterpret (L := ℒₒᵣ).mpr;
    apply h;
  . intro h f;
    replace h := iff_provable_boxdot_GL_provable_Grz.mpr h;
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

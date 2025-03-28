import Foundation.Modal.Boxdot.GL_Grz

namespace LO.Modal

namespace Kripke

open Relation (ReflGen)
open Formula.Kripke

variable {F : Frame} {φ : Formula _}

end Kripke

namespace Hilbert

open Kripke
open Formula.Kripke
open Formula (BoxdotTranslation)
open Modal.Kripke
open Entailment

lemma provable_boxdotTranslated_GLPoint3_of_GrzPoint3 : (Hilbert.GrzPoint3) ⊢! φ → (Hilbert.GLPoint3) ⊢! φᵇ := boxdotTranslated_of_dominate $ by
  intro φ hp;
  rcases (by simpa using hp) with (⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨s, _, rfl⟩);
  . exact boxdot_axiomK!;
  . exact boxdot_Grz_of_L!
  . apply Hilbert.GLPoint3.Kripke.finite_complete.complete;
    rintro F ⟨_, _, _⟩ V x;
    apply Satisfies.or_def.mpr;
    by_contra hC;
    push_neg at hC;
    obtain ⟨hC₁, hC₂⟩ := hC;
    replace hC₁ := not_and_or.mp $ Satisfies.and_def.not.mp hC₁;
    replace hC₂ := not_and_or.mp $ Satisfies.and_def.not.mp hC₂;
    rcases hC₁ with (hC₁ | hC₁) <;>
    rcases hC₂ with (hC₂ | hC₂)
    . replace hC₁ := Satisfies.imp_def₂.not.mp hC₁;
      replace hC₂ := Satisfies.imp_def₂.not.mp hC₂;
      push_neg at hC₁ hC₂;
      tauto;
    . replace hC₁ := Satisfies.imp_def₂.not.mp hC₁;
      replace hC₂ := Satisfies.box_def.not.mp hC₂;
      push_neg at hC₁ hC₂;
      obtain ⟨hC₁₁, hC₁₂⟩ := hC₁;
      obtain ⟨hC₁₁₁, hC₁₂₁⟩ := Satisfies.and_def.mp hC₁₁
      obtain ⟨y, Rxy, hC₂⟩ := hC₂;
      replace hC₂ := Satisfies.imp_def₂.not.mp hC₂;
      push_neg at hC₂;
      exact hC₂.2 $ hC₁₂₁ y Rxy;
    . replace hC₁ := Satisfies.box_def.not.mp hC₁;
      replace hC₂ := Satisfies.imp_def₂.not.mp hC₂;
      push_neg at hC₁ hC₂;
      obtain ⟨y, Rxy, hC₁⟩ := hC₁;
      replace hC₁ := Satisfies.imp_def₂.not.mp hC₁;
      push_neg at hC₁;
      obtain ⟨hC₂₁, hC₂₂⟩ := hC₂;
      obtain ⟨hC₂₁₁, hC₂₂₁⟩ := Satisfies.and_def.mp hC₂₁
      exact hC₁.2 $ hC₂₂₁ y Rxy;
    . replace hC₁ := Satisfies.box_def.not.mp hC₁;
      replace hC₂ := Satisfies.box_def.not.mp hC₂;
      push_neg at hC₁ hC₂;
      obtain ⟨y, Rxy, hC₁⟩ := hC₁;
      obtain ⟨z, Rxz, hC₂⟩ := hC₂;
      replace hC₁ := Satisfies.imp_def₂.not.mp hC₁;
      replace hC₂ := Satisfies.imp_def₂.not.mp hC₂;
      push_neg at hC₁ hC₂;
      obtain ⟨hC₁₁, hC₁₂⟩ := hC₁;
      obtain ⟨hC₁₁₁, hC₁₁₂⟩ := Satisfies.and_def.mp hC₁₁
      obtain ⟨hC₂₁, hC₂₂⟩ := hC₂;
      obtain ⟨hC₂₁₁, hC₂₁₂⟩ := Satisfies.and_def.mp hC₂₁
      rcases IsWeakConnected.weak_connected ⟨Rxy, Rxz, by by_contra eyz; subst eyz; tauto⟩ with (Ryz | Rzy);
      . exact hC₂₂ $ hC₁₁₂ z Ryz;
      . exact hC₁₂ $ hC₂₁₂ y Rzy;

lemma provable_GrzPoint3_of_boxdotTranslated_GLPoint3 : (Hilbert.GLPoint3) ⊢! φᵇ → (Hilbert.GrzPoint3) ⊢! φ := by
  contrapose;
  intro h;
  obtain ⟨F, ⟨_, _, _⟩, h⟩ := iff_not_validOnFrameClass_exists_frame.mp $ (not_imp_not.mpr $ Hilbert.GrzPoint3.Kripke.finite_complete |>.complete) h;
  apply not_imp_not.mpr $ Hilbert.GLPoint3.Kripke.finite_sound.sound;
  apply iff_not_validOnFrameClass_exists_frame.mpr;
  use F^≠;
  constructor;
  . refine ⟨inferInstance, inferInstance, inferInstance⟩;
  . apply Kripke.iff_frame_boxdot_reflexive_closure.not.mpr;
    apply iff_reflexivize_irreflexivize'.not.mp;
    exact h;

theorem iff_boxdotTranslatedGLPoint3_GrzPoint3 : (Hilbert.GLPoint3) ⊢! φᵇ ↔ (Hilbert.GrzPoint3) ⊢! φ := ⟨
  provable_GrzPoint3_of_boxdotTranslated_GLPoint3,
  provable_boxdotTranslated_GLPoint3_of_GrzPoint3
⟩

end Hilbert

instance : BoxdotProperty (Logic.GLPoint3) (Logic.GrzPoint3) := ⟨Hilbert.iff_boxdotTranslatedGLPoint3_GrzPoint3⟩

end LO.Modal

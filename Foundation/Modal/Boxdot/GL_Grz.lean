import Foundation.Modal.Boxdot.Basic
import Foundation.Modal.Logic.WellKnown

namespace LO.Modal

namespace Kripke

open Relation (ReflGen)
open Formula.Kripke

variable {F : Frame} {φ : Formula _}

lemma mem_reflClosure_GrzFiniteFrameClass_of_mem_GLFiniteFrameClass (hF : F ∈ FrameClass.finite_trans_irrefl) : F^= ∈ FrameClass.finite_partial_order := by
  obtain ⟨_, _, _⟩ := hF;
  refine ⟨inferInstance, inferInstance⟩;

lemma mem_irreflClosure_GLFiniteFrameClass_of_mem_GrzFiniteFrameClass (hF : F ∈ FrameClass.finite_partial_order) : F^≠ ∈ FrameClass.finite_trans_irrefl := by
  obtain ⟨_, _, F_trans, F_antisymm⟩ := hF;
  refine ⟨inferInstance, inferInstance, inferInstance⟩;

lemma iff_boxdot_reflexive_closure : (Satisfies ⟨F, V⟩ x (φᵇ)) ↔ (Satisfies ⟨F^=, V⟩ x φ) := by
  induction φ generalizing x with
  | himp φ ψ ihp ihq =>
    constructor;
    . intro h hp;
      apply ihq.mp;
      exact h $ ihp.mpr hp;
    . intro h hp;
      apply ihq.mpr;
      exact h $ ihp.mp hp;
  | hbox φ ih =>
    dsimp [Formula.BoxdotTranslation];
    constructor;
    . intro h;
      replace ⟨h₁, h₂⟩ := Satisfies.and_def.mp h;
      intro y Rxy;
      rcases (Relation.reflGen_iff _ _ _ |>.mp Rxy) with (rfl | Rxy);
      . apply ih.mp h₁;
      . exact ih.mp $ h₂ y Rxy;
    . rintro h;
      apply Satisfies.and_def.mpr;
      constructor;
      . exact ih.mpr $ @h x ReflGen.refl;
      . intro y Rxy;
        apply ih.mpr;
        exact @h y (ReflGen.single Rxy);
  | _ => rfl;

lemma iff_frame_boxdot_reflexive_closure : (F ⊧ (φᵇ)) ↔ ((F^=) ⊧ φ) := by
  constructor;
  . intro h V x; apply iff_boxdot_reflexive_closure.mp; exact h V x;
  . intro h V x; apply iff_boxdot_reflexive_closure.mpr; exact h V x;

lemma iff_reflexivize_irreflexivize [IsRefl _ F] {x : F.World} {V} : (Satisfies ⟨F, V⟩ x φ) ↔ (Satisfies ⟨F^≠^=, V⟩ x φ) := by
  induction φ generalizing x with
  | hatom φ => rfl;
  | hfalsum => rfl;
  | himp φ ψ ihp ihq =>
    constructor;
    . intro h hp;
      apply ihq.mp;
      exact h $ ihp.mpr hp;
    . intro h hp;
      apply ihq.mpr;
      exact h $ ihp.mp hp;
  | hbox φ ihp =>
    constructor;
    . intro h y Rxy;
      apply ihp (x := y) |>.mp;
      exact h y $ by
        induction Rxy with
        | refl => apply IsRefl.refl;
        | single h => exact h.2;
    . intro h y Rxy;
      by_cases e : x = y;
      . subst e;
        apply ihp.mpr;
        exact h x ReflGen.refl;
      . apply ihp (x := y) |>.mpr;
        exact h y $ by
          exact ReflGen.single ⟨(by simpa), Rxy⟩;

lemma iff_reflexivize_irreflexivize' [IsRefl _ F] : (F ⊧ φ) ↔ ((F^≠^=) ⊧ φ) := by
  constructor;
  . intro h V x; apply iff_reflexivize_irreflexivize.mp; exact h V x;
  . intro h V x; apply iff_reflexivize_irreflexivize.mpr; exact h V x;

end Kripke


namespace Hilbert

open Kripke
open Formula.Kripke
open Formula (BoxdotTranslation)
open Modal.Kripke
open Entailment


lemma provable_boxdotTranslated_GL_of_Grz : (Hilbert.Grz) ⊢! φ → (Hilbert.GL) ⊢! φᵇ := boxdotTranslated_of_dominate $ by
  intro φ hp;
  rcases (by simpa using hp) with (⟨_, _, rfl⟩ | ⟨_, rfl⟩);
  . exact boxdot_axiomK!;
  . exact boxdot_Grz_of_L!

lemma provable_Grz_of_boxdotTranslated_GL : (Hilbert.GL) ⊢! φᵇ → (Hilbert.Grz) ⊢! φ := by
  contrapose;
  intro h;
  obtain ⟨F, ⟨_, _, _⟩, h⟩ := iff_not_validOnFrameClass_exists_frame.mp $ (not_imp_not.mpr $ Hilbert.Grz.Kripke.complete |>.complete) h;
  apply not_imp_not.mpr $ Hilbert.GL.Kripke.finite_sound.sound;
  apply iff_not_validOnFrameClass_exists_frame.mpr;
  use F^≠;
  constructor;
  . refine ⟨inferInstance, inferInstance, inferInstance⟩;
  . apply Kripke.iff_frame_boxdot_reflexive_closure.not.mpr;
    apply iff_reflexivize_irreflexivize'.not.mp;
    exact h;

theorem iff_boxdotTranslatedGL_Grz : (Hilbert.GL) ⊢! φᵇ ↔ (Hilbert.Grz) ⊢! φ := ⟨
  provable_Grz_of_boxdotTranslated_GL,
  provable_boxdotTranslated_GL_of_Grz
⟩

end Hilbert

instance : BoxdotProperty (Logic.GL) (Logic.Grz) := ⟨Hilbert.iff_boxdotTranslatedGL_Grz⟩

end LO.Modal

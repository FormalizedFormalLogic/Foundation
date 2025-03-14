import Foundation.Modal.Boxdot.Basic
import Foundation.Modal.Logic.WellKnown

namespace LO.Modal

namespace Kripke

open Relation (ReflGen)
open Formula.Kripke

lemma mem_reflClosure_GrzFiniteFrameClass_of_mem_GLFiniteFrameClass (hF : F ∈ FrameClass.finite_trans_irrefl) : F^= ∈ FrameClass.finite_partial_order := by
  obtain ⟨_, F_trans, F_irrefl⟩ := hF;
  refine ⟨inferInstance, ?F_refl, ?F_trans, ?F_antisymm⟩;
  . intro x; apply ReflGen.refl;
  . rintro x y z (rfl | Rxy) (rfl | Ryz);
    . apply ReflGen.refl;
    . apply ReflGen.single Ryz;
    . apply ReflGen.single Rxy;
    . apply ReflGen.single $ F_trans Rxy Ryz;
  . rintro x y (rfl | Rxy) (rfl | Ryx);
    . rfl;
    . rfl;
    . rfl;
    . have := F_trans Rxy Ryx;
      have := F_irrefl x;
      contradiction;

lemma mem_irreflClosure_GLFiniteFrameClass_of_mem_GrzFiniteFrameClass (hF : F ∈ FrameClass.finite_partial_order) : F^≠ ∈ FrameClass.finite_trans_irrefl := by
  obtain ⟨_, _, F_trans, F_antisymm⟩ := hF;
  refine ⟨inferInstance, ?F_trans, ?F_irrefl⟩;
  . rintro x y z ⟨nexy, Rxy⟩ ⟨_, Ryz⟩;
    constructor;
    . by_contra; subst_vars;
      have := F_antisymm Rxy Ryz;
      contradiction;
    . exact F_trans Rxy Ryz;
  . simp;

lemma iff_boxdot_reflexive_closure : (Satisfies ⟨F, V⟩ x (φᵇ)) ↔ (Satisfies ⟨F^=, V⟩ x φ) := by
  induction φ using Formula.rec' generalizing x with
  | himp φ ψ ihp ihq =>
    constructor;
    . intro h hp;
      apply ihq.mp;
      exact h $ ihp.mpr hp;
    . intro h hp;
      apply ihq.mpr;
      exact h $ ihp.mp hp;
  | hbox φ ih =>
    simp [Formula.BoxdotTranslation, Box.boxdot, Satisfies];
    constructor;
    . rintro ⟨h₁, h₂⟩;
      intro y Rxy;
      rcases (Relation.reflGen_iff _ _ _ |>.mp Rxy) with (rfl | Rxy);
      . apply ih.mp h₁;
      . exact ih.mp $ h₂ y Rxy;
    . rintro h;
      constructor;
      . exact ih.mpr $ @h x ReflGen.refl;
      . intro y Rxy;
        apply ih.mpr;
        exact @h y (ReflGen.single Rxy);
  | _ => rfl;

lemma iff_frame_boxdot_reflexive_closure {F : Frame} : (F ⊧ (φᵇ)) ↔ ((F^=) ⊧ φ) := by
  constructor;
  . intro h V x; apply iff_boxdot_reflexive_closure.mp; exact h V x;
  . intro h V x; apply iff_boxdot_reflexive_closure.mpr; exact h V x;

lemma iff_reflexivize_irreflexivize {F : Frame} (F_Refl : Reflexive F) {x : F.World} {V} : (Satisfies ⟨F, V⟩ x φ) ↔ (Satisfies ⟨F^≠^=, V⟩ x φ) := by
  induction φ using Formula.rec' generalizing x with
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
        | refl => apply F_Refl
        | single h => exact h.2;
    . intro h y Rxy;
      by_cases e : x = y;
      . subst e;
        apply ihp.mpr;
        exact h x ReflGen.refl;
      . apply ihp (x := y) |>.mpr;
        exact h y $ by
          exact ReflGen.single ⟨(by simpa), Rxy⟩;

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
  obtain ⟨F, ⟨_, F_refl, F_trans, F_antisymm⟩, h⟩ := iff_not_validOnFrameClass_exists_frame.mp $ (not_imp_not.mpr $ Hilbert.Grz.Kripke.complete |>.complete) h;
  apply not_imp_not.mpr $ Hilbert.GL.Kripke.finite_sound.sound;
  apply iff_not_validOnFrameClass_exists_frame.mpr;
  use F^≠;
  constructor;
  . suffices Transitive (F^≠).Rel by refine ⟨inferInstance, by assumption, by simp⟩;
    rintro x y z ⟨hxy, Rxy⟩ ⟨hyz, Ryz⟩;
    constructor;
    . by_contra hC;
      subst hC;
      have := F_antisymm Rxy Ryz;
      contradiction;
    . exact F_trans Rxy Ryz;
  . apply Kripke.iff_frame_boxdot_reflexive_closure.not.mpr;
    apply Formula.Kripke.ValidOnFrame.not_of_exists_valuation_world;
    obtain ⟨V, x, hx⟩ := Formula.Kripke.ValidOnFrame.iff_not_exists_valuation_world.mp h;
    use V, x;
    exact iff_reflexivize_irreflexivize F_refl |>.not.mp hx;

theorem iff_boxdotTranslatedGL_Grz : (Hilbert.GL) ⊢! φᵇ ↔ (Hilbert.Grz) ⊢! φ := ⟨
  provable_Grz_of_boxdotTranslated_GL,
  provable_boxdotTranslated_GL_of_Grz
⟩

end Hilbert

instance : BoxdotProperty (Logic.GL) (Logic.Grz) := ⟨Hilbert.iff_boxdotTranslatedGL_Grz⟩

end LO.Modal

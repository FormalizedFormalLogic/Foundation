import Foundation.Logic.Kripke.Closure
import Foundation.Modal.Boxdot.Basic
import Foundation.Modal.Kripke.Grz.Completeness
import Foundation.Modal.Kripke.GL.Completeness

namespace LO.Modal

namespace Kripke

open Relation (ReflGen)
open LO.Kripke
open Formula.Kripke

lemma mem_reflClosure_GrzFiniteFrameClass_of_mem_GLFiniteFrameClass (hF : F ∈ TransitiveIrreflexiveFrameClassꟳ) : ⟨F^=⟩ ∈ ReflexiveTransitiveAntisymmetricFrameClassꟳ := by
  obtain ⟨F_trans, F_irrefl⟩ := hF;
  refine ⟨?F_refl, ?F_trans, ?F_antisymm⟩;
  . intro x; apply ReflGen.refl;
  . rintro x y z (rfl | Rxy) (rfl | Ryz);
    . apply ReflGen.refl;
    . apply ReflGen.single Ryz;
    . apply ReflGen.single Rxy;
    . apply ReflGen.single $ F_trans Rxy Ryz;
  . simp;
    rintro x y (rfl | Rxy) (rfl | Ryx);
    . rfl;
    . rfl;
    . rfl;
    . have := F_trans Rxy Ryx;
      have := F_irrefl x;
      contradiction;

lemma mem_irreflClosure_GLFiniteFrameClass_of_mem_GrzFiniteFrameClass (hF : F ∈ ReflexiveTransitiveAntisymmetricFrameClassꟳ) : ⟨F^≠⟩ ∈ TransitiveIrreflexiveFrameClassꟳ := by
  obtain ⟨_, F_trans, F_antisymm⟩ := hF;
  refine ⟨?F_trans, ?F_irrefl⟩;
  . rintro x y z ⟨nexy, Rxy⟩ ⟨_, Ryz⟩;
    constructor;
    . by_contra; subst_vars;
      have := F_antisymm Rxy Ryz;
      contradiction;
    . exact F_trans Rxy Ryz;
  . simp;

variable {φ : Formula α}

lemma iff_boxdot_reflexive_closure : (Satisfies ⟨F, V⟩ x (φᵇ)) ↔ (Satisfies ⟨F^=, V⟩ x φ) := by
  induction φ using Formula.rec' generalizing x with
  | hatom φ => simp [Satisfies];
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
  | _ => simp_all [Satisfies];

lemma iff_frame_boxdot_reflexive_closure {F : Frame} : (F#α ⊧ (φᵇ)) ↔ ((F^=)#α ⊧ φ) := by
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

open Formula.Kripke
open Kripke

variable {α : Type u} [DecidableEq α]
variable {φ : Formula α}

open Formula (BoxdotTranslation)
open System in
lemma boxdotTranslatedGL_of_Grz : (Hilbert.Grz α) ⊢! φ → (Hilbert.GL α) ⊢! φᵇ := boxdotTranslated $ by
  intro φ hp;
  rcases hp with (⟨_, _, rfl⟩ | ⟨_, rfl⟩);
  . dsimp [BoxdotTranslation]; exact boxdot_axiomK!;
  . dsimp [BoxdotTranslation]; exact boxdot_Grz_of_L!

lemma Grz_of_boxdotTranslatedGL [Inhabited α] : (Hilbert.GL α) ⊢! φᵇ → (Hilbert.Grz α) ⊢! φ := by
  contrapose;
  intro h;
  apply (not_imp_not.mpr $ Kripke.GL_finite_sound.sound);
  have := (not_imp_not.mpr $ Grz_complete |>.complete) h;
  simp at this;
  obtain ⟨F, FF, ⟨FF_refl, FF_trans, FF_antisymm, rfl, hFF⟩⟩ := this;
  simp;
  use FF^≠, ⟨FF^≠⟩;
  refine ⟨?_, ?_, ?_, ?_⟩;
  . rintro x y z ⟨Rxy₂, Rxy⟩ ⟨Ryz₂, Ryz⟩;
    refine ⟨?_, FF_trans Rxy Ryz⟩
    by_contra hC; subst hC;
    have := FF_antisymm Rxy Ryz;
    contradiction;
  . simp;
  . rfl;
  . apply Kripke.iff_frame_boxdot_reflexive_closure.not.mpr;
    simp_all [ValidOnFrame, ValidOnModel];
    obtain ⟨V, x, h⟩ := hFF;
    use V, x;
    exact iff_reflexivize_irreflexivize FF_refl |>.not.mp h;

theorem iff_Grz_boxdotTranslatedGL [Inhabited α] : (Hilbert.Grz α) ⊢! φ ↔ (Hilbert.GL α) ⊢! φᵇ := by
  constructor;
  . apply boxdotTranslatedGL_of_Grz;
  . apply Grz_of_boxdotTranslatedGL;

instance [Inhabited α] : BoxdotProperty (Hilbert.Grz α) (Hilbert.GL α) := ⟨iff_Grz_boxdotTranslatedGL⟩

end LO.Modal

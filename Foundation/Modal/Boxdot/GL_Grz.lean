import Foundation.Modal.Boxdot.Basic
import Foundation.Modal.Kripke.Closure
import Foundation.Modal.Kripke.Grz.Completeness
import Foundation.Modal.Kripke.GL.Completeness

namespace LO.Modal

namespace Kripke

open Relation (ReflGen)
open Formula.Kripke

lemma mem_reflClosure_GrzFiniteFrameClass_of_mem_GLFiniteFrameClass (hF : F ∈ TransitiveIrreflexiveFiniteFrameClass) : ⟨F.toFrame^=⟩ ∈ ReflexiveTransitiveAntiSymmetricFiniteFrameClass := by
  obtain ⟨F_trans, F_irrefl⟩ := hF;
  refine ⟨?F_refl, ?F_trans, ?F_antisymm⟩;
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

lemma mem_irreflClosure_GLFiniteFrameClass_of_mem_GrzFiniteFrameClass (hF : F ∈ ReflexiveTransitiveAntiSymmetricFiniteFrameClass) : ⟨F.toFrame^≠⟩ ∈ TransitiveIrreflexiveFiniteFrameClass := by
  obtain ⟨_, F_trans, F_antisymm⟩ := hF;
  refine ⟨?F_trans, ?F_irrefl⟩;
  . rintro x y z ⟨nexy, Rxy⟩ ⟨_, Ryz⟩;
    constructor;
    . by_contra; subst_vars;
      have := F_antisymm Rxy Ryz;
      contradiction;
    . exact F_trans Rxy Ryz;
  . simp;

variable {φ : Formula ℕ}

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
open Hilbert.Kripke
open Modal.Kripke


variable {φ : Formula ℕ}

open System in
lemma boxdotTranslatedGL_of_Grz : (Hilbert.Grz ℕ) ⊢! φ → (Hilbert.GL ℕ) ⊢! φᵇ := boxdotTranslated $ by
  intro φ hp;
  rcases hp with (⟨_, _, rfl⟩ | ⟨_, rfl⟩);
  . dsimp [BoxdotTranslation]; exact boxdot_axiomK!;
  . dsimp [BoxdotTranslation]; exact boxdot_Grz_of_L!

lemma Grz_of_boxdotTranslatedGL : (Hilbert.GL ℕ) ⊢! φᵇ → (Hilbert.Grz ℕ) ⊢! φ := by
  contrapose;
  intro h;
  apply (not_imp_not.mpr $ Hilbert.GL.Kripke.finite_sound.sound);
  have := (not_imp_not.mpr $ Hilbert.Grz.Kripke.complete |>.complete) h;
  simp [FiniteFrameClass.toFrameClass] at this;
  obtain ⟨F, FF, ⟨FF_refl, FF_trans, FF_antisymm, rfl, hFF⟩⟩ := this;
  simp;
  use FF.toFrame^≠;
  constructor;
  . use ⟨FF.toFrame^≠⟩;
    simp [Transitive];
    rintro x y z ⟨hxy, Rxy⟩ ⟨hyz, Ryz⟩;
    constructor;
    . by_contra hC;
      subst hC;
      have := FF_antisymm Rxy Ryz;
      contradiction;
    . exact FF_trans Rxy Ryz;
  . apply Kripke.iff_frame_boxdot_reflexive_closure.not.mpr;
    simp_all [ValidOnFrame, ValidOnModel];
    obtain ⟨V, x, h⟩ := hFF;
    use V, x;
    exact iff_reflexivize_irreflexivize FF_refl |>.not.mp h;

theorem iff_Grz_boxdotTranslatedGL : (Hilbert.GL ℕ) ⊢! φᵇ ↔ (Hilbert.Grz ℕ) ⊢! φ := by
  constructor;
  . apply Grz_of_boxdotTranslatedGL;
  . apply boxdotTranslatedGL_of_Grz;

instance : BoxdotProperty (Hilbert.GL ℕ) (Hilbert.Grz ℕ) := ⟨iff_Grz_boxdotTranslatedGL⟩

end Hilbert

end LO.Modal

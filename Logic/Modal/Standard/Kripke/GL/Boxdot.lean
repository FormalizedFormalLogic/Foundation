import Logic.Modal.Standard.Kripke.Grz.Completeness
import Logic.Modal.Standard.Kripke.GL.Completeness
import Logic.Modal.Standard.Boxdot

namespace LO.Modal.Standard

namespace Kripke

open Relation

protected abbrev Frame.RelReflGen {F : Frame} : _root_.Rel F.World F.World := ReflGen (· ≺ ·)
scoped infix:45 " ≺^r " => Frame.RelReflGen

abbrev Frame.ReflexiveClosure (F : Frame) : Frame where
  World := F.World
  Rel := (· ≺^r ·)
postfix:max "^r" => Frame.ReflexiveClosure


protected abbrev Frame.RelIrreflGen {F : Frame} := λ x y => (x ≠ y) ∧ (F.Rel x y)
scoped infix:45 " ≺^ir " => Frame.RelIrreflGen

abbrev Frame.IrreflexiveClosure (F : Frame) : Frame where
  World := F.World
  Rel := (· ≺^ir ·)
postfix:max "^ir" => Frame.IrreflexiveClosure

open Formula.Kripke

lemma reflexivize (hF : F ∈ TransitiveIrreflexiveFrameClassꟳ) : F^r ∈ ReflexiveTransitiveAntisymmetricFrameClassꟳ := by
  obtain ⟨FF, ⟨FF_trans, FF_irrefl⟩, hFF₂⟩ := hF;
  use ⟨FF.World, ReflGen $ FF.Rel⟩;
  constructor;
  . refine ⟨?F_refl, ?F_trans, ?F_antisymm⟩;
    . intro x; apply ReflGen.refl;
    . simp;
      rintro x y z (rfl | Rxy) (rfl | Ryz);
      . apply ReflGen.refl;
      . apply ReflGen.single Ryz;
      . apply ReflGen.single Rxy;
      . apply ReflGen.single $ FF_trans Rxy Ryz;
    . simp;
      rintro x y (rfl | Rxy) (rfl | Ryx);
      . rfl;
      . rfl;
      . rfl;
      . have := FF_trans Rxy Ryx;
        have := FF_irrefl x;
        contradiction;
  . subst_vars; aesop;

lemma irreflexive (hF : F ∈ ReflexiveTransitiveAntisymmetricFrameClassꟳ) : F^ir ∈ TransitiveIrreflexiveFrameClassꟳ := by
  obtain ⟨FF, ⟨_, FF_trans, FF_antisymm⟩, rfl⟩ := hF;
  use ⟨FF.World, λ x y => x ≠ y ∧ FF.Rel x y⟩;
  simp;
  refine ⟨?F_trans, ?F_irrefl⟩;
  . rintro x y z ⟨nexy, Rxy⟩ ⟨_, Ryz⟩;
    constructor;
    . by_contra; subst_vars;
      have := FF_antisymm Rxy Ryz;
      contradiction;
    . exact FF_trans Rxy Ryz;
  . simp [Irreflexive];

variable {p : Formula α}

lemma iff_boxdot_reflexive_closure : (Satisfies ⟨F, V⟩ x (pᵇ)) ↔ (Satisfies ⟨F^r, V⟩ x p) := by
  induction p using Formula.rec' generalizing x with
  | hatom p => simp [Satisfies];
  | hbox p ih =>
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

lemma iff_frame_boxdot_reflexive_closure {F : Frame} : (F# ⊧ (pᵇ)) ↔ (F^r# ⊧ p) := by
  constructor;
  . intro h V x; apply iff_boxdot_reflexive_closure.mp; exact h V x;
  . intro h V x; apply iff_boxdot_reflexive_closure.mpr; exact h V x;

lemma iff_reflexivize_irreflexivize {F : Frame} (F_Refl : Reflexive F) {x : F.World} {V} : (Satisfies ⟨F, V⟩ x p) ↔ (Satisfies ⟨F^ir^r, V⟩ x p) := by
  induction p using Formula.rec' generalizing x with
  | hatom p => rfl;
  | hfalsum => rfl;
  | himp p q ihp ihq =>
    constructor;
    . intro h hp;
      apply ihq.mp;
      exact h $ ihp.mpr hp;
    . intro h hp;
      apply ihq.mpr;
      exact h $ ihp.mp hp;
  | hbox p ihp =>
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

variable {α : Type u} [Inhabited α] [DecidableEq α]
variable {p : Formula α}

open Formula (BoxdotTranslation)
open System in
lemma boxdotTranslatedGL_of_Grz : 𝐆𝐫𝐳 ⊢! p → 𝐆𝐋 ⊢! pᵇ := boxdotTranslated $ by
  intro p hp;
  rcases hp with (⟨_, _, rfl⟩ | ⟨_, rfl⟩);
  . dsimp [BoxdotTranslation]; exact boxdot_axiomK!;
  . dsimp [BoxdotTranslation]; exact boxdot_Grz_of_L!

lemma Grz_of_boxdotTranslatedGL : 𝐆𝐋 ⊢! pᵇ → 𝐆𝐫𝐳 ⊢! p := by
  contrapose;
  intro h;
  apply (not_imp_not.mpr $ Kripke.GL_sound.sound);
  have := (not_imp_not.mpr $ Grz_complete |>.complete) h;
  simp at this;
  obtain ⟨F, ⟨F_refl, F_trans, F_antisymm⟩, hF⟩ := this;
  simp;
  use F^ir, ⟨F^ir⟩;
  refine ⟨?_, ?_, ?_, ?_⟩;
  . rintro x y z ⟨Rxy₂, Rxy⟩ ⟨Ryz₂, Ryz⟩;
    refine ⟨?_, F_trans Rxy Ryz⟩
    by_contra hC; subst hC;
    have := F_antisymm Rxy Ryz;
    contradiction;
  . simp [Irreflexive];
  . rfl;
  . apply Kripke.iff_frame_boxdot_reflexive_closure.not.mpr;
    simp_all [ValidOnFrame, ValidOnModel];
    obtain ⟨V, x, h⟩ := hF;
    use V, x;
    exact iff_reflexivize_irreflexivize F_refl |>.not.mp h;

theorem iff_Grz_boxdotTranslatedGL : 𝐆𝐫𝐳 ⊢! p ↔ 𝐆𝐋 ⊢! pᵇ := by
  constructor;
  . apply boxdotTranslatedGL_of_Grz;
  . apply Grz_of_boxdotTranslatedGL;

end LO.Modal.Standard

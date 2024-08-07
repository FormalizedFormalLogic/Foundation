import Logic.Modal.Standard.Kripke.GL.Completeness
import Logic.Modal.Standard.Boxdot

namespace LO.Modal.Standard

namespace Kripke

open Relation

protected abbrev Frame.RelReflGen {F : Frame} : _root_.Rel F.World F.World:= ReflGen (· ≺ ·)
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

abbrev ReflexiveTransitiveAntisymmetricFrameClass : FrameClass := { F | Reflexive F ∧ Transitive F ∧ Antisymmetric F }

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
      . exact ih.mp $ h₂ Rxy;
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

end Kripke

open Formula.Kripke

variable {α : Type u} [Inhabited α] [DecidableEq α]
variable {p : Formula α}

lemma Grz_of_boxdotTranslatedGL
  (Grz_sound : Sound (𝐆𝐫𝐳 : DeductionParameter α) (Kripke.ReflexiveTransitiveAntisymmetricFrameClass.{u}ꟳ.alt))
  : 𝐆𝐫𝐳 ⊢! p → 𝐆𝐋 ⊢! pᵇ := by
  contrapose;
  intro h;
  have := (not_imp_not.mpr $ Kripke.GL_complete |>.complete) h;
  simp [ValidOnFrame, ValidOnModel] at this;
  obtain ⟨F, FF, F_trans, F_irrefl, e₁, V, x, hx⟩ := this;
  have s := Kripke.iff_boxdot_reflexive_closure.not.mp hx;

  have H := Kripke.reflexivize (F := FF) (⟨FF, ⟨F_trans, F_irrefl⟩, rfl⟩);
  simp at H;
  obtain ⟨FF₂, ⟨F_refl, F_trans, F_antisymm⟩, e₂⟩ := H;
  apply (not_imp_not.mpr $ Grz_sound.sound (f := p));

  simp [ValidOnFrameClass, ValidOnFrame, ValidOnModel];
  use F^r, FF₂;
  refine ⟨F_refl, F_trans, F_antisymm, ?_, ?_⟩
  . subst e₁; exact e₂;
  . use V, x;


lemma Grz_of_boxdotTranslatedGL2
  (Grz_complete : Complete (𝐆𝐫𝐳 : DeductionParameter α) (Kripke.ReflexiveTransitiveAntisymmetricFrameClass.{u}ꟳ.alt))
  : 𝐆𝐋 ⊢! pᵇ → 𝐆𝐫𝐳 ⊢! p := by
  contrapose;
  intro h;
  have := (not_imp_not.mpr $ Grz_complete |>.complete) h;
  simp at this;
  obtain ⟨F, FF, FF_refl, FF_trans, FF_antisymm, _, h⟩ := this;
  have := @Kripke.iff_frame_boxdot_reflexive_closure α p (FF^ir);

  apply (not_imp_not.mpr $ Kripke.GL_sound.sound);
  simp;
  use FF^ir, FF;
  refine ⟨?F_trans, ?F_refl, ?a, ?b⟩;
  . sorry;
  . sorry;
  . sorry;
  . apply (@Kripke.iff_frame_boxdot_reflexive_closure α p (FF^ir)).not.mpr;
    sorry;


theorem iff_Grz_boxdotTranslatedGL
  (Grz_complete : Complete (𝐆𝐫𝐳 : DeductionParameter α) (Kripke.ReflexiveTransitiveAntisymmetricFrameClass.{u}ꟳ.alt))
  : 𝐆𝐫𝐳 ⊢! p ↔ 𝐆𝐋 ⊢! pᵇ := by
  constructor;
  . apply boxdotTranslatedGL_of_Grz;
  . apply Grz_of_boxdotTranslatedGL2 Grz_complete;

end LO.Modal.Standard

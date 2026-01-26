module

public import Foundation.Modal.Kripke.Logic.GrzPoint2
public import Foundation.Modal.Kripke.Logic.S4Point3

@[expose] public section

namespace LO.Modal

open Formula
open Formula.Kripke
open Entailment
open Entailment.Context
open Kripke


open Entailment
open Entailment.Context
open Formula
open Formula.Kripke
open Modal.Kripke
open Kripke

namespace Kripke

variable {F : Frame}

protected class Frame.IsFiniteGrzPoint3 (F : Frame) extends F.IsFinite, F.IsPartialOrder, F.IsStronglyConnected where
protected class Frame.IsFiniteGrzPoint3' (F : Frame) extends F.IsFinite, F.IsPartialOrder, F.IsPiecewiseStronglyConnected where

abbrev FrameClass.finite_GrzPoint3 : FrameClass := { F | F.IsFiniteGrzPoint3  }

instance [F.IsFiniteGrzPoint3] : F.IsFiniteGrzPoint2 where

instance : whitepoint.IsStronglyConnected := ⟨by tauto⟩

end Kripke

instance : Sound Modal.GrzPoint3 FrameClass.finite_GrzPoint3 := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomGrz_of_finite_strict_preorder;
  . exact validate_axiomPoint3_of_isPiecewiseStronglyConnected;

instance : Sound Modal.GrzPoint3 { F : Frame | F.IsFiniteGrzPoint3' } := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  rintro _ (rfl | rfl) F ⟨_, _⟩;
  . exact validate_AxiomGrz_of_finite_strict_preorder;
  . exact validate_axiomPoint3_of_isPiecewiseStronglyConnected;

instance : Entailment.Consistent Modal.GrzPoint3 :=
  consistent_of_sound_frameclass FrameClass.finite_GrzPoint3 $ by
    use whitepoint;
    constructor;

instance : Complete Modal.GrzPoint3 FrameClass.finite_GrzPoint3 :=
  Modal.Grz.Kripke.complete_of_mem_miniCanonicalFrame FrameClass.finite_GrzPoint3 $ by
    sorry;
    /-
    intro φ;
    refine ⟨miniCanonicalFrame.reflexive, miniCanonicalFrame.transitive, miniCanonicalFrame.antisymm, ?_⟩;
    intro x y z ⟨⟨Rxy₁, Rxy₂⟩, ⟨Rxz₁, Rxz₂⟩⟩;
    apply or_iff_not_imp_left.mpr;
    intro nRyz;
    rcases (not_and_or.mp nRyz) with (nRyz | nRyz);
    . push_neg at nRyz;
      obtain ⟨ψ, hψ, ⟨hψy, hψz⟩⟩ := nRyz;
      constructor;
      . intro ξ hξ₁ hξ₂;
        apply Rxy₁;
        . exact hξ₁;
        . sorry;
      . intro hyz;
        have exy := Rxy₂ ?_;
        have exz := Rxz₂ ?_;
        tauto;
        . subst exy;
          intro ξ hξ hξz;
          sorry;
        . intro ξ hξ hξy;
          sorry;
    . push_neg at nRyz;
      replace ⟨nRyz₁, nRyz₂⟩ := nRyz;
      constructor;
      . sorry;
      . sorry;
    -/

namespace Logic

open Formula
open Entailment
open Kripke


instance : Modal.GrzPoint2 ⪱ Modal.GrzPoint3 := by
  constructor;
  . apply Modal.Kripke.weakerThan_of_subset_frameClass FrameClass.finite_GrzPoint2 FrameClass.finite_GrzPoint3;
    intro F hF;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Point3 (.atom 0) (.atom 1);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.finite_GrzPoint2);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let F : Frame := ⟨Fin 4, λ x y => x = 0 ∨ x = y ∨ y = 3⟩;
      let M : Model := ⟨
        F,
        λ x a => match a with | 0 => (1 : F.World) ≺ x | 1 => (2 : F.World) ≺ x | _ => False
      ⟩;
      use M, 0;
      constructor;
      . exact {
          refl := by omega,
          trans := by omega,
          antisymm := by simp [M, F]; omega,
          ps_convergent := by
            rintro x y z Rxy Rxz;
            use 3;
            tauto;
        }
      . apply Satisfies.or_def.not.mpr
        push_neg;
        constructor;
        . apply Satisfies.box_def.not.mpr;
          push_neg;
          use 1;
          constructor;
          . tauto;
          . apply Satisfies.imp_def₂.not.mpr;
            push_neg;
            constructor;
            . tauto;
            . simp [M, Semantics.Models, Satisfies, Frame.Rel', F];
        . apply Satisfies.box_def.not.mpr;
          push_neg;
          use 2;
          constructor;
          . tauto;
          . apply Satisfies.imp_def₂.not.mpr;
            push_neg;
            constructor;
            . tauto;
            . simp [M, Semantics.Models, Satisfies, Frame.Rel', F];

instance : Modal.S4Point3 ⪱ Modal.GrzPoint3 := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_provable_axioms;
    rintro _ (rfl | rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Grz (.atom 0);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.S4Point3);
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 1⟩, 0;
      constructor;
      . exact {
          refl := by simp,
          trans := by simp,
          ps_connected := by
            rintro x y z Rxy Rxz;
            simp;
        };
      . simp [Semantics.Models, Satisfies];

end Logic



end LO.Modal
end

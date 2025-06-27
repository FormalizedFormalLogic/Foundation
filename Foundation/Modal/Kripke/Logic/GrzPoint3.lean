import Foundation.Modal.Kripke.Logic.GrzPoint2
import Foundation.Modal.Kripke.Logic.S4Point3

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
open Hilbert.Kripke
open Kripke

namespace Kripke

variable {F : Frame}

protected class Frame.IsFiniteGrzPoint3 (F : Frame) extends F.IsFinite, F.IsPartialOrder, F.IsPiecewiseStronglyConnected where

abbrev FrameClass.finite_connected_partial_order : FrameClass := { F | F.IsFiniteGrzPoint3  }

instance [F.IsFiniteGrzPoint3] : F.IsFiniteGrzPoint2 where

end Kripke


namespace Logic.GrzPoint3.Kripke

instance finite_sound : Sound Logic.GrzPoint3 FrameClass.finite_connected_partial_order := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _⟩ _ (rfl | rfl);
  . exact validate_AxiomGrz_of_finite_strict_preorder;
  . exact validate_axiomPoint3_of_isPiecewiseStronglyConnected;

instance consistent : Entailment.Consistent Logic.GrzPoint3 :=
  consistent_of_sound_frameclass FrameClass.finite_connected_partial_order $ by
    use whitepoint;
    constructor;

instance finite_complete : Complete Logic.GrzPoint3 FrameClass.finite_connected_partial_order :=
  Grz.Kripke.complete_of_mem_miniCanonicalFrame FrameClass.finite_connected_partial_order $ by
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

end Logic.GrzPoint3.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma GrzPoint3.Kripke.finite_connected_partial_order : Logic.GrzPoint3 = FrameClass.finite_connected_partial_order.logic := eq_hilbert_logic_frameClass_logic

theorem GrzPoint3.proper_extension_of_GrzPoint2: Logic.GrzPoint2 ⪱ Logic.GrzPoint3 := by
  constructor;
  . apply Entailment.weakerThan_iff.mpr;
    suffices ∀ φ, FrameClass.finite_GrzPoint2 ⊧ φ → FrameClass.finite_connected_partial_order ⊧ φ by
      simpa [GrzPoint2.Kripke.finite_confluent_partial_order, GrzPoint3.Kripke.finite_connected_partial_order];
    rintro φ hφ F hF;
    apply hφ;
    simp_all only [Set.mem_setOf_eq];
    infer_instance;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.GrzPoint3 ⊢! φ ∧ ¬FrameClass.finite_GrzPoint2 ⊧ φ by simpa [GrzPoint2.Kripke.finite_confluent_partial_order];
    use Axioms.Point3 (.atom 0) (.atom 1);
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
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
            . simp [M, Semantics.Realize, Satisfies, Frame.Rel', F];
        . apply Satisfies.box_def.not.mpr;
          push_neg;
          use 2;
          constructor;
          . tauto;
          . apply Satisfies.imp_def₂.not.mpr;
            push_neg;
            constructor;
            . tauto;
            . simp [M, Semantics.Realize, Satisfies, Frame.Rel', F];

instance : Logic.S4Point3 ⪱ Logic.GrzPoint3 := by
  constructor;
  . apply Hilbert.weakerThan_of_provable_axioms;
    rintro _ (rfl | rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.GrzPoint3 ⊢! φ ∧ ¬FrameClass.finite_S4Point3 ⊧ φ by simpa [S4Point3.Kripke.finite_connected_preorder];
    use Axioms.Grz (.atom 0);
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 1⟩, 0;
      constructor;
      . exact {
          refl := by simp,
          trans := by simp,
          ps_connected := by
            rintro x y z Rxy Rxz;
            simp;
        };
      . simp [Reflexive, Transitive, Semantics.Realize, Satisfies];
@[deprecated] instance : Logic.S4Point3 ⪯ Logic.GrzPoint3 := Entailment.StrictlyWeakerThan.weakerThan

end Logic


end LO.Modal

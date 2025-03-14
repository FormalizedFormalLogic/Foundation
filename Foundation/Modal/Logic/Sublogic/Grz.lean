import Foundation.Modal.Logic.Sublogic.S5Grz

namespace LO.Modal.Logic

open Formula
open Entailment
open Kripke

theorem S4_ssubset_Grz : Logic.S4 ⊂ Logic.Grz := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.Grz ⊢! φ ∧ ¬Kripke.FrameClass.preorder ⊧ φ by simpa [S4.eq_ReflexiveTransitiveKripkeFrameClass_Logic];
    use Axioms.Grz (.atom 0)
    constructor;
    . exact axiomGrz!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 1⟩, 0;
      simp [Reflexive, Transitive, Semantics.Realize, Satisfies];
instance : ProperSublogic Logic.S4 Logic.Grz := ⟨S4_ssubset_Grz⟩

lemma Grz_ssubset_S5Grz : Logic.Grz ⊂ Logic.S5Grz := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.S5Grz ⊢! φ ∧ ¬FrameClass.finite_partial_order ⊧ φ by simpa [Grz.eq_ReflexiveTransitiveAntiSymmetricFiniteKripkeFrameClass_Logic];
    use Axioms.Five (.atom 0)
    constructor;
    . exact axiomFive!;
    . apply Kripke.not_validOnFrameClass_of_exists_frame;
      let F : Frame := ⟨Fin 2, λ x y => x ≤ y⟩;
      use F;
      constructor;
      . refine ⟨by tauto, ?_, ?_, ?_⟩;
        . simp [F, Reflexive];
        . simp [F, Transitive]; omega;
        . simp [F, AntiSymmetric]; omega;
      . apply ValidOnFrame.not_of_exists_valuation_world;
        use (λ w _ => w = 0), 0;
        suffices (0 : F.World) ≺ 0 ∧ ∃ x, (0 : F.World) ≺ x ∧ ¬x ≺ 0 by
          simpa [Semantics.Realize, Satisfies, ValidOnFrame];
        constructor;
        . omega;
        . use 1;
          constructor <;> omega;

theorem Grz_ssubset_Triv : Logic.Grz ⊂ Logic.Triv := by
  convert Grz_ssubset_S5Grz;
  exact S5Grz_eq_Triv.symm;
instance : ProperSublogic Logic.Grz Logic.Triv := ⟨Grz_ssubset_Triv⟩


instance : ProperSublogic Logic.Grz Logic.GrzPoint2 := ⟨by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.GrzPoint2 ⊢! φ ∧ ¬FrameClass.finite_partial_order ⊧ φ by
      simpa [Grz.eq_ReflexiveTransitiveAntiSymmetricFiniteKripkeFrameClass_Logic];
    use Axioms.Point2 (.atom 0);
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 3, λ x y => x = 0 ∨ x = y⟩,
        λ x a => x = 1
      ⟩;
      use M, 0;
      constructor;
      . simp only [Fin.isValue, Set.mem_setOf_eq, M];
        refine ⟨?_, ?_, ?_, ?_⟩;
        . tauto;
        . simp [Reflexive];
        . simp [Transitive]; omega;
        . simp [AntiSymmetric]; omega;
      . apply Satisfies.imp_def₂.not.mpr;
        push_neg;
        constructor;
        . apply Satisfies.dia_def.mpr;
          use 1;
          constructor;
          . omega;
          . intro y Rxy; simp_all [M, Semantics.Realize, Satisfies, Frame.Rel'];
        . apply Satisfies.box_def.not.mpr;
          push_neg;
          use 2;
          constructor;
          . omega;
          . apply Satisfies.dia_def.not.mpr;
            push_neg;
            simp [M, Semantics.Realize, Satisfies, Frame.Rel'];
⟩

theorem S4Point2_ssubset_GrzPoint2 : Logic.S4Point2 ⊂ Logic.GrzPoint2 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . sorry;
instance : ProperSublogic Logic.S4Point2 Logic.GrzPoint2 := ⟨S4Point2_ssubset_GrzPoint2⟩


instance : ProperSublogic Logic.GrzPoint2 Logic.GrzPoint3 := ⟨by
  constructor;
  . rw [GrzPoint2.eq_ReflexiveTransitiveAntiSymmetricConfluentFiniteKripkeFrameClass_Logic, GrzPoint3.eq_ReflexiveTransitiveAntiSymmetricConnectedFiniteKripkeFrameClass_Logic];
    rintro φ hφ F ⟨_, F_refl, F_trans, F_antisymm, F_conn⟩;
    apply hφ;
    refine ⟨inferInstance, F_refl, F_trans, F_antisymm, ?_⟩;
    . rintro x y z ⟨Rxy, Ryz⟩;
      rcases F_conn ⟨Rxy, Ryz⟩ with (Ryz | Rzy);
      . use z; tauto;
      . use y; tauto
  . suffices ∃ φ, Hilbert.GrzPoint3 ⊢! φ ∧ ¬FrameClass.finite_confluent_partial_order ⊧ φ by
      simpa [GrzPoint2.eq_ReflexiveTransitiveAntiSymmetricConfluentFiniteKripkeFrameClass_Logic];
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
      . simp only [Fin.isValue, Set.mem_setOf_eq, M, F];
        refine ⟨?_, ?_, ?_, ?_, ?_⟩;
        . tauto;
        . simp [Reflexive];
        . simp [Transitive]; omega;
        . simp [AntiSymmetric]; omega;;
        . rintro x y z ⟨(_ | _ | Rxy), (_ | _ | Rxy)⟩;
          repeat { use 3; tauto; }
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
⟩

theorem S4Point3_ssubset_GrzPoint3 : Logic.S4Point3 ⊂ Logic.GrzPoint3 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . sorry;
instance : ProperSublogic Logic.S4Point3 Logic.GrzPoint3 := ⟨S4Point3_ssubset_GrzPoint3⟩

end LO.Modal.Logic

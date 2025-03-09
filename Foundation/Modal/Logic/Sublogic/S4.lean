import Foundation.Modal.Logic.WellKnown

namespace LO.Modal.Logic

open Formula
open Entailment
open Kripke

theorem S4_ssubset_S4Point2 : Logic.S4 ⊂ Logic.S4Point2 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.S4Point2 ⊢! φ ∧ ¬FrameClass.preorder ⊧ φ by simpa [S4.eq_ReflexiveTransitiveKripkeFrameClass_Logic];
    use Axioms.Point2 (.atom 0)
    constructor;
    . exact axiomPoint2!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => (x = 0) ∨ (x = y) ⟩, λ w _ => w = 1⟩;
      use M, 0;
      constructor;
      . constructor;
        . simp [M, Reflexive];
        . unfold Transitive;
          omega;
      . suffices ∃ x, (0 : M.World) ≺ x ∧ (∀ y, x ≺ y → y = 1) ∧ ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 1 by
          simpa [M, Semantics.Realize, Satisfies];
        use 1;
        refine ⟨by omega, ?_, ?_⟩;
        . intro y;
          match y with
          | 0 => omega;
          | 1 => tauto;
          | 2 => omega;
        . use 2;
          constructor;
          . omega;
          . omega;
instance : ProperSublogic Logic.S4 Logic.S4Point2 := ⟨S4_ssubset_S4Point2⟩


theorem S4Point2_ssubset_S4Point3 : Logic.S4Point2 ⊂ Logic.S4Point3 := by
  constructor;
  . rw [S4Point2.eq_ReflexiveTransitiveConfluentKripkeFrameClass_Logic, S4Point3.eq_ReflexiveTransitiveConnectedKripkeFrameClass_Logic];
    rintro φ hφ F ⟨F_refl, F_trans, F_conn⟩;
    apply hφ;
    refine ⟨?_, ?_, ?_⟩;
    . exact F_refl;
    . exact F_trans;
    . exact confluent_of_refl_connected F_refl F_conn;
  . suffices ∃ φ, Hilbert.S4Point3 ⊢! φ ∧ ¬FrameClass.confluent_preorder ⊧ φ by
      simpa [S4Point2.eq_ReflexiveTransitiveConfluentKripkeFrameClass_Logic];
    use Axioms.Point3 (.atom 0) (.atom 1);
    constructor;
    . exact axiomPoint3!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 4, λ x y => ¬(x = 1 ∧ y = 2) ∧ ¬(x = 2 ∧ y = 1) ∧ (x ≤ y)⟩, λ w a => (a = 0 ∧ (w = 1 ∨ w = 3)) ∨ (a = 1 ∧ (w = 2 ∨ w = 3))⟩;
      use M, 0;
      constructor;
      . simp only [Set.mem_setOf_eq];
        refine ⟨?_, ?_, ?_⟩;
        . simp [M, Reflexive]; omega;
        . simp [M, Transitive]; omega;
        . rintro x y z ⟨Rxy, Ryz⟩;
          use 3;
          constructor <;> omega;
      . apply Kripke.Satisfies.or_def.not.mpr;
        push_neg;
        constructor;
        . apply Kripke.Satisfies.box_def.not.mpr;
          push_neg;
          use 1;
          simp [Satisfies, Semantics.Realize, M];
          constructor <;> omega;
        . apply Kripke.Satisfies.box_def.not.mpr;
          push_neg;
          use 2;
          simp [Satisfies, Semantics.Realize, M];
          constructor <;> omega;
instance : ProperSublogic Logic.S4Point2 Logic.S4Point3 := ⟨S4Point2_ssubset_S4Point3⟩

lemma S4_ssubset_S4Point3 : Logic.S4 ⊂ Logic.S4Point3 := by
  transitivity Logic.S4Point2;
  exact S4_ssubset_S4Point2;
  exact S4Point2_ssubset_S4Point3;

theorem S4Point3_ssubset_S5 : Logic.S4Point3 ⊂ Logic.S5 := by
  constructor;
  . rw [S4Point3.eq_ReflexiveTransitiveConnectedKripkeFrameClass_Logic, S5.eq_UniversalKripkeFrameClass_Logic];
    rintro φ hφ F F_univ;
    apply hφ;
    refine ⟨?_, ?_, ?_⟩;
    . unfold Reflexive; intros; apply F_univ;
    . unfold Transitive; intros; apply F_univ;
    . unfold Connected; intros; constructor; apply F_univ;
  . suffices ∃ φ, Hilbert.S5 ⊢! φ ∧ ¬FrameClass.connected_preorder ⊧ φ by
      simpa [S4Point3.eq_ReflexiveTransitiveConnectedKripkeFrameClass_Logic];
    use Axioms.Five (.atom 0);
    constructor;
    . exact axiomFive!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≤ y⟩, λ w a => (w = 0)⟩;
      use M, 0;
      constructor;
      . simp only [Set.mem_setOf_eq];
        refine ⟨?_, ?_, ?_⟩;
        . simp [M, Reflexive];
        . simp [M, Transitive]; omega;
        . rintro x y z ⟨Rxy, Ryz⟩; omega;
      . suffices (0 : M.World) ≺ 0 ∧ ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 0 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . omega;
        . use 1;
          constructor <;> omega;
instance : ProperSublogic Logic.S4Point3 Logic.S5 := ⟨S4Point3_ssubset_S5⟩

end LO.Modal.Logic

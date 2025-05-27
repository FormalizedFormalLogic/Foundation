import Foundation.Modal.Kripke.Logic.S4Point1
import Foundation.Modal.Kripke.Logic.S4Point2
import Foundation.Modal.Kripke.Logic.S4Point3
import Foundation.Modal.Kripke.Logic.S5

namespace LO.Modal.Logic

open Formula
open Entailment
open Kripke

instance : ProperSublogic Logic.S4 Logic.S4Point1 := ⟨by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.S4Point1 ⊢! φ ∧ ¬FrameClass.preorder ⊧ φ by
      rw [S4.Kripke.preorder];
      tauto;
    use (Axioms.M (.atom 0));
    constructor;
    . exact axiomM!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 0⟩;
      use M, 0;
      constructor;
      . apply isPreorder_iff _ _ |>.mpr;
        refine ⟨⟨?_⟩, ⟨?_⟩⟩ <;> simp [M];
      . suffices ∃ x, x ≠ (0 : M.World) by simpa [M, Transitive, Reflexive, Semantics.Realize, Satisfies];
        use 1;
        trivial;
⟩

theorem S4_ssubset_S4Point2 : Logic.S4 ⊂ Logic.S4Point2 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.S4Point2 ⊢! φ ∧ ¬FrameClass.preorder ⊧ φ by
      rw [S4.Kripke.preorder];
      tauto;
    use Axioms.Point2 (.atom 0)
    constructor;
    . exact axiomPoint2!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => (x = 0) ∨ (x = y) ⟩, λ w _ => w = 1⟩;
      use M, 0;
      constructor;
      . apply isPreorder_iff _ _ |>.mpr;
        refine ⟨⟨?_⟩, ⟨?_⟩⟩ <;> omega;
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
  . rw [S4Point2.Kripke.confluent_preorder, S4Point3.Kripke.connected_preorder];
    rintro φ hφ F ⟨_, _⟩;
    apply hφ;
    refine ⟨inferInstance, inferInstance⟩;
  . suffices ∃ φ, Hilbert.S4Point3 ⊢! φ ∧ ¬FrameClass.confluent_preorder ⊧ φ by
      rw [S4Point2.Kripke.confluent_preorder];
      tauto;
    use Axioms.Point3 (.atom 0) (.atom 1);
    constructor;
    . exact axiomPoint3!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 4, λ x y => ¬(x = 1 ∧ y = 2) ∧ ¬(x = 2 ∧ y = 1) ∧ (x ≤ y)⟩,
        λ w a => (a = 0 ∧ (w = 1 ∨ w = 3)) ∨ (a = 1 ∧ (w = 2 ∨ w = 3))
      ⟩;
      use M, 0;
      constructor;
      . apply Set.mem_setOf_eq.mpr
        refine ⟨?_, ⟨?_⟩⟩;
        . apply isPreorder_iff _ _ |>.mpr;
          refine ⟨⟨by omega⟩, ⟨by omega⟩⟩;
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
  . rw [S4Point3.Kripke.connected_preorder, S5.Kripke.universal];
    rintro φ hφ F F_univ;
    apply hφ;
    replace F_univ := Set.mem_setOf_eq.mp F_univ
    refine ⟨inferInstance, inferInstance⟩;
  . suffices ∃ φ, Hilbert.S5 ⊢! φ ∧ ¬FrameClass.connected_preorder ⊧ φ by
      rw [S4Point3.Kripke.connected_preorder];
      tauto;
    use Axioms.Five (.atom 0);
    constructor;
    . exact axiomFive!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≤ y⟩, λ w a => (w = 0)⟩;
      use M, 0;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        refine ⟨?_, ⟨?_⟩⟩;
        . apply isPreorder_iff _ _ |>.mpr;
          refine ⟨⟨by omega⟩, ⟨by omega⟩⟩;
        . rintro x y z ⟨Rxy, Ryz⟩; omega;
      . suffices (0 : M.World) ≺ 0 ∧ ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 0 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . omega;
        . use 1;
          constructor <;> omega;
instance : ProperSublogic Logic.S4Point3 Logic.S5 := ⟨S4Point3_ssubset_S5⟩

end LO.Modal.Logic

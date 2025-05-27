import Foundation.Modal.Kripke.Logic.K4
import Foundation.Modal.Kripke.Logic.K4Point1
import Foundation.Modal.Kripke.Logic.K4Point2
import Foundation.Modal.Kripke.Logic.K4Point3
import Foundation.Modal.Kripke.Logic.S4Point1
import Foundation.Modal.Kripke.Logic.S4Point2
import Foundation.Modal.Kripke.Logic.S4Point3
import Foundation.Modal.Kripke.Logic.K45

namespace LO.Modal.Logic

open Formula
open Entailment
open Kripke

instance : ProperSublogic Logic.K4 Logic.K4Point1 := ⟨by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.K4Point1 ⊢! φ ∧ ¬Kripke.FrameClass.trans ⊧ φ by
      rw [K4.Kripke.trans];
      tauto;
    use (Axioms.M (.atom 0));
    constructor;
    . exact axiomM!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ w _ => False⟩, 0;
      constructor;
      . refine ⟨by tauto⟩;
      . simp [Semantics.Realize, Satisfies];
⟩

instance : ProperSublogic Logic.K4 Logic.K4Point2 := ⟨by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.K4Point2 ⊢! φ ∧ ¬Kripke.FrameClass.trans ⊧ φ by
      rw [K4.Kripke.trans];
      tauto;
    use (Axioms.WeakPoint2 (.atom 0) (.atom 1));
    constructor;
    . exact axiomWeakPoint2!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 2, λ x y => x = 0⟩,
        λ w a => if a = 0 then True else w = 0
      ⟩;
      use M, 0;
      constructor;
      . refine ⟨by tauto⟩;
      . suffices ∃ (x : M.World), (∀ y, ¬x ≺ y) ∧ x ≠ 0 by
          simpa [M, Semantics.Realize, Satisfies];
        use 1;
        constructor;
        . omega;
        . trivial;
⟩

instance : ProperSublogic Logic.K4Point2 Logic.S4Point2 := ⟨by
  constructor;
  . rw [K4Point2.Kripke.trans_weakConfluent, S4Point2.Kripke.confluent_preorder];
    rintro φ hφ F ⟨_, _⟩;
    apply hφ;
    refine ⟨inferInstance, inferInstance⟩;
  . suffices ∃ φ, Hilbert.S4Point2 ⊢! φ ∧ ¬Kripke.FrameClass.trans_weakConfluent ⊧ φ by
      rw [K4Point2.Kripke.trans_weakConfluent];
      tauto;
    use (Axioms.Point2 (.atom 0));
    constructor;
    . exact axiomPoint2!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 2, λ x y => x < y⟩,
        λ w a => False
      ⟩;
      use M, 0;
      constructor;
      . refine ⟨⟨by omega⟩, ⟨?_⟩⟩;
        . simp [M, WeakConfluent]; omega;
      . suffices ∃ x, (0 : M.World) ≺ x ∧ (∀ y, ¬x ≺ y) ∧ ∃ x, (0 : M.World) ≺ x by
          simpa [M, Semantics.Realize, Satisfies];
        use 1;
        refine ⟨?_, ?_, ?_⟩;
        . omega;
        . omega;
        . use 1; omega;
⟩


instance : ProperSublogic Logic.K4 Logic.K4Point3 := ⟨by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.K4Point3 ⊢! φ ∧ ¬Kripke.FrameClass.trans ⊧ φ by
      rw [K4.Kripke.trans];
      tauto;
    use (Axioms.WeakPoint3 (.atom 0) (.atom 1));
    constructor;
    . exact axiomWeakPoint3!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 3, λ x y => x = 0 ∧ y ≠ 0⟩,
        λ w a => if a = 0 then w = 1 else w = 2
      ⟩;
      use M, 0;
      constructor;
      . refine ⟨by omega⟩
      . suffices
          ∃ x : M.World, (0 : M.World) ≺ x ∧ x = 1 ∧ (∀ y, x ≺ y → y = 1) ∧ ¬x = 2 ∧
          ∃ x : M.World, (0 : M.World) ≺ x ∧ x = 2 ∧ (∀ z : M.World, x ≺ z → z = 2) ∧ x ≠ 1
          by simpa [M, Semantics.Realize, Satisfies];
        refine ⟨1, ?_, rfl, ?_, ?_, 2, ?_, rfl, ?_, ?_⟩;
        . trivial;
        . omega;
        . trivial;
        . omega;
        . trivial;
        . trivial;
⟩

instance : ProperSublogic Logic.K4Point3 Logic.S4Point3 := ⟨by
  constructor;
  . rw [K4Point3.Kripke.trans_weakConnected, S4Point3.Kripke.connected_preorder];
    rintro φ hφ F ⟨_, _⟩;
    apply hφ;
    refine ⟨inferInstance, inferInstance⟩;
  . suffices ∃ φ, Hilbert.S4Point3 ⊢! φ ∧ ¬Kripke.FrameClass.trans_weakConnected ⊧ φ by
      rw [K4Point3.Kripke.trans_weakConnected];
      tauto;
    use (Axioms.Point3 (.atom 0) (.atom 1));
    constructor;
    . exact axiomPoint3!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 2, λ x y => x < y⟩,
        λ w a => False
      ⟩;
      use M, 0;
      constructor;
      . refine ⟨⟨by omega⟩, ⟨by simp [M, WeakConnected]⟩⟩
      . suffices ∃ x, (0 : M.World) ≺ x ∧ (∀ y, ¬x ≺ y) ∧ ∃ x, (0 : M.World) ≺ x ∧ ∀ y, ¬x ≺ y by
          simpa [M, Semantics.Realize, Satisfies];
        use 1;
        refine ⟨?_, ?_, ⟨1, ?_, ?_⟩⟩;
        repeat omega;
⟩

instance : ProperSublogic Logic.K4Point3 Logic.K45 := ⟨by
  constructor;
  . rw [K4Point3.Kripke.trans_weakConnected, K45.Kripke.trans_eucl];
    rintro φ hφ F ⟨_, _⟩;
    apply hφ;
    refine ⟨inferInstance, inferInstance⟩;
  . suffices ∃ φ, Hilbert.K45 ⊢! φ ∧ ¬Kripke.FrameClass.trans_weakConnected ⊧ φ by
      rw [K4Point3.Kripke.trans_weakConnected];
      tauto;
    use (Axioms.Five (.atom 0));
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 3, λ x y => x < y⟩,
        λ w a => w = 2
      ⟩;
      use M, 0;
      constructor;
      . refine ⟨⟨by omega⟩, ⟨by simp [M, WeakConnected]⟩⟩
      . suffices (0 : M.World) ≺ 2 ∧ ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 2 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . omega;
        . use 2;
          omega;
⟩

end LO.Modal.Logic

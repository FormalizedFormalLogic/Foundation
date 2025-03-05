import Foundation.Modal.Logic.WellKnown

namespace LO.Modal.Logic

open Formula
open Entailment
open Kripke

instance : ProperSublogic Logic.K4 Logic.K4Point2 := ⟨by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.K4Point2 ⊢! φ ∧ ¬TransitiveFrameClass ⊧ φ by simpa [K4.eq_TransitiveKripkeFrameClass_Logic];
    use (Axioms.WeakPoint2 (.atom 0) (.atom 1));
    constructor;
    . exact axiomWeakPoint2!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 2, λ x y => x = 0⟩,
        λ w a => if a = 0 then True else w = 0
      ⟩;
      use M, 0;
      constructor;
      . simp [Transitive, M];
      . suffices ∃ (x : M.World), (∀ y, ¬x ≺ y) ∧ x ≠ 0 by
          simpa [M, Semantics.Realize, Satisfies];
        use 1;
        constructor;
        . omega;
        . trivial;
⟩

instance : ProperSublogic Logic.K4Point2 Logic.S4Point2 := ⟨by
  constructor;
  . rw [K4Point2.eq_TransitiveWeakConfluentKripkeFrameClass_Logic, S4Point2.eq_ReflexiveTransitiveConfluentKripkeFrameClass_Logic];
    rintro φ hφ F ⟨F_refl, F_trans, F_conn⟩;
    apply hφ;
    refine ⟨F_trans, ?_⟩;
    . rintro x y z ⟨Rxy, Ryz, _⟩;
      exact F_conn ⟨Rxy, Ryz⟩;
  . suffices ∃ φ, Hilbert.S4Point2 ⊢! φ ∧ ¬TransitiveWeakConfluentFrameClass ⊧ φ by simpa [K4Point2.eq_TransitiveWeakConfluentKripkeFrameClass_Logic];
    use (Axioms.Point2 (.atom 0));
    constructor;
    . exact axiomPoint2!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 2, λ x y => x < y⟩,
        λ w a => False
      ⟩;
      use M, 0;
      constructor;
      . unfold M;
        constructor;
        . simp [Transitive]; omega;
        . simp [WeakConfluent]; omega;
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
  . suffices ∃ φ, Hilbert.K4Point3 ⊢! φ ∧ ¬TransitiveFrameClass ⊧ φ by simpa [K4.eq_TransitiveKripkeFrameClass_Logic];
    use (Axioms.WeakPoint3 (.atom 0) (.atom 1));
    constructor;
    . exact axiomWeakPoint3!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 3, λ x y => x = 0 ∧ y ≠ 0⟩,
        λ w a => if a = 0 then w = 1 else w = 2
      ⟩;
      use M, 0;
      constructor;
      . simp [M, Transitive];
        omega;
      . suffices
          ∃ x : M.World, (0 : M.World) ≺ x ∧ x = 1 ∧ (∀ y, x ≺ y → y = 1) ∧ ¬x = 2 ∧ ∃ x : M.World, (0 : M.World) ≺ x ∧ x = 2 ∧ (∀ z : M.World, x ≺ z → z = 2) ∧ x ≠ 1
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
  . rw [K4Point3.eq_TransitiveWeakConnectedKripkeFrameClass_Logic, S4Point3.eq_ReflexiveTransitiveConnectedKripkeFrameClass_Logic];
    rintro φ hφ F ⟨F_refl, F_trans, F_conn⟩;
    apply hφ;
    refine ⟨F_trans, ?_⟩;
    . rintro x y z ⟨Rxy, Ryz, _⟩;
      exact F_conn ⟨Rxy, Ryz⟩;
  . suffices ∃ φ, Hilbert.S4Point3 ⊢! φ ∧ ¬TransitiveWeakConnectedFrameClass ⊧ φ by simpa [K4Point3.eq_TransitiveWeakConnectedKripkeFrameClass_Logic];
    use (Axioms.Point3 (.atom 0) (.atom 1));
    constructor;
    . exact axiomPoint3!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      let M : Model := ⟨
        ⟨Fin 2, λ x y => x < y⟩,
        λ w a => False
      ⟩;
      use M, 0;
      constructor;
      . unfold M;
        constructor;
        . simp [Transitive]; omega;
        . simp [WeakConnected];
      . suffices ∃ x, (0 : M.World) ≺ x ∧ (∀ y, ¬x ≺ y) ∧ ∃ x, (0 : M.World) ≺ x ∧ ∀ y, ¬x ≺ y by
          simpa [M, Semantics.Realize, Satisfies];
        use 1;
        refine ⟨?_, ?_, ⟨1, ?_, ?_⟩⟩;
        repeat omega;
⟩

end LO.Modal.Logic

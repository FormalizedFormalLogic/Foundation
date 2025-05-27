import Foundation.Modal.Logic.Sublogic.K4
import Foundation.Modal.Maximal.Unprovability
import Foundation.Modal.Entailment.GL
import Foundation.Modal.Kripke.Hilbert.GL.Unnecessitation
import Foundation.Modal.Kripke.Hilbert.GLPoint3
import Foundation.Modal.Kripke.Hilbert.Ver

namespace LO.Modal.Logic

open Formula
open Entailment
open Kripke

theorem K4_ssubset_GL : Logic.K4 ⊂ Logic.GL := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.GL ⊢! φ ∧ ¬Hilbert.K4 ⊢! φ by tauto;
    use (Axioms.L (.atom 0));
    constructor;
    . exact axiomL!;
    . exact Hilbert.K4.unprovable_AxiomL;
instance : ProperSublogic Logic.K4 Logic.GL := ⟨K4_ssubset_GL⟩

theorem GL_ssubset_Ver : Logic.GL ⊂ Logic.Ver := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.Ver ⊢! φ ∧ ¬Hilbert.GL ⊢! φ by tauto;
    use (Axioms.Ver ⊥);
    constructor;
    . exact axiomVer!;
    . by_contra hC;
      have := unnec! hC;
      have := Hilbert.GL.Kripke.consistent.not_bot;
      contradiction
instance : ProperSublogic Logic.GL Logic.Ver := ⟨GL_ssubset_Ver⟩

theorem GL_ssubset_GLPoint3 : Logic.GL ⊂ Logic.GLPoint3 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.GLPoint3 ⊢! φ ∧ ¬Kripke.FrameClass.finite_trans_irrefl ⊧ φ by
      rw [GL.Kripke.finite_trans_irrefl];
      tauto;
    use (Axioms.WeakPoint3 (.atom 0) (.atom 1));
    constructor;
    . simp;
    . let M : Model := ⟨⟨Fin 3, λ x y => (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2)⟩, (λ w a => match a with | 0 => w = 1 | 1 => w = 2 | _ => False)⟩;
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use M, 0;
      constructor;
      . refine ⟨inferInstance, ⟨by omega⟩, ⟨by omega⟩⟩
      . suffices (0 : M.World) ≺ 1 ∧ (∀ x, (1 : M.World) ≺ x → x = 1) ∧ (0 : M.World) ≺ 2 ∧ ∀ x, (2 : M.World) ≺ x → x = 2 by
          simpa [Semantics.Realize, Satisfies, ValidOnFrame, M];
        refine ⟨?_, ?_, ?_, ?_⟩;
        all_goals omega;
instance : ProperSublogic Logic.GL Logic.GLPoint3 := ⟨GL_ssubset_GLPoint3⟩

theorem K4Point3_ssubset_GLPoint3 : Logic.K4Point3 ⊂ Logic.GLPoint3 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.GLPoint3 ⊢! φ ∧ ¬Kripke.FrameClass.trans_weakConnected ⊧ φ by
      rw [K4Point3.Kripke.trans_weakConnected];
      tauto;
    use (Axioms.L (.atom 0));
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => x ≤ y⟩, (λ w a => False)⟩, 0;
      constructor;
      . refine ⟨⟨by omega⟩, ⟨by simp only [WeakConnected, ne_eq, and_imp]; omega⟩⟩;
      . simp [Semantics.Realize, Satisfies, ValidOnFrame];
        constructor;
        . intro y Rxy;
          use y;
        . use 1;
          omega;
instance : ProperSublogic Logic.K4Point3 Logic.GLPoint3 := ⟨K4Point3_ssubset_GLPoint3⟩

theorem GLPoint3_ssubset_Ver : Logic.GLPoint3 ⊂ Logic.Ver := by
  constructor;
  . rw [GLPoint3.Kripke.finite_strict_linear_order, Ver.Kripke.finite_isolated];
    rintro φ hφ F ⟨_, _⟩;
    apply hφ;
    refine ⟨by tauto, inferInstance, inferInstance⟩;
  . suffices ∃ φ, Hilbert.Ver ⊢! φ ∧ ¬FrameClass.finite_strict_linear_order ⊧ φ by
      rw [GLPoint3.Kripke.finite_strict_linear_order];
      tauto;
    use (Axioms.Ver ⊥);
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => x < y⟩, (λ w a => False)⟩, 0;
      constructor;
      . refine ⟨inferInstance, {irrefl := ?_, trans := ?_}, ⟨?_⟩⟩;
        . omega;
        . omega;
        . simp [WeakConnected];
      . simp only [Semantics.Realize, Satisfies, imp_false, not_forall, not_not];
        use 1;
        tauto;
instance : ProperSublogic Logic.GLPoint3 Logic.Ver := ⟨GLPoint3_ssubset_Ver⟩

end LO.Modal.Logic

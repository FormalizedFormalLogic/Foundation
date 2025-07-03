import Foundation.Modal.Kripke.Logic.GL.Completeness
import Foundation.Modal.Kripke.Logic.K4Point3

namespace LO.Modal

open Entailment
open Entailment.Context
open Formula
open Formula.Kripke
open Hilbert.Kripke
open Kripke

namespace Kripke

protected class Frame.IsFiniteGLPoint3 (F : Frame) extends F.IsFiniteGL, F.IsPiecewiseConnected

abbrev FrameClass.finite_GLPoint3 : FrameClass := { F | F.IsFiniteGLPoint3 }

instance : blackpoint.IsFiniteGLPoint3 where
  p_connected := by tauto;

end Kripke


namespace Logic.GLPoint3.Kripke

instance finite_sound : Sound Logic.GLPoint3 FrameClass.finite_GLPoint3 := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _⟩ _ (rfl | rfl);
  . exact validate_AxiomL_of_finite_trans_irrefl;
  . exact validate_WeakPoint3_of_weakConnected;

instance consistent : Entailment.Consistent Logic.GLPoint3 :=
  consistent_of_sound_frameclass FrameClass.finite_GLPoint3 $ by
    use blackpoint;
    constructor;

instance finite_complete : Complete Logic.GLPoint3 FrameClass.finite_GLPoint3 := by sorry;

lemma finite_strict_linear_order : Logic.GLPoint3 = FrameClass.finite_GLPoint3.logic := eq_hilbert_logic_frameClass_logic

instance : Logic.GL ⪱ Logic.GLPoint3 := by
  constructor;
  . apply Hilbert.weakerThan_of_provable_axioms;
    rintro _ (rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.GLPoint3 ⊢! φ ∧ ¬Kripke.FrameClass.finite_GL ⊧ φ by simpa [GL.Kripke.finite_trans_irrefl];
    use (Axioms.WeakPoint3 (.atom 0) (.atom 1));
    constructor;
    . simp;
    . let M : Model := ⟨⟨Fin 3, λ x y => (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2)⟩, (λ w a => match a with | 0 => w = 1 | 1 => w = 2 | _ => False)⟩;
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use M, 0;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        exact {
          trans := by omega,
          irrefl := by omega
        };
      . suffices (0 : M.World) ≺ 1 ∧ (∀ x, (1 : M.World) ≺ x → x = 1) ∧ (0 : M.World) ≺ 2 ∧ ∀ x, (2 : M.World) ≺ x → x = 2 by
          simpa [Semantics.Realize, Satisfies, ValidOnFrame, M];
        refine ⟨?_, ?_, ?_, ?_⟩;
        all_goals omega;

instance : Logic.K4Point3 ⪱ Logic.GLPoint3 := by
  constructor;
  . apply Hilbert.weakerThan_of_provable_axioms;
    rintro _ (rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    suffices ∃ φ, Logic.GLPoint3 ⊢! φ ∧ ¬FrameClass.IsK4Point3 ⊧ φ by simpa [K4Point3.Kripke.trans_weakConnected];
    use (Axioms.L (.atom 0));
    constructor;
    . simp;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => x ≤ y⟩, (λ w a => False)⟩, 0;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        constructor;
      . simp [Semantics.Realize, Satisfies, ValidOnFrame];
        constructor;
        . intro y Rxy;
          use y;
        . use 1;
          omega;

end Logic.GLPoint3.Kripke

end LO.Modal

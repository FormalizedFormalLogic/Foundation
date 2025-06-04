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

abbrev FrameClass.finite_strict_linear_order : FrameClass := { F | Finite F.World ∧ IsStrictOrder _ F.Rel ∧ IsWeakConnected _ F.Rel }

end Kripke


namespace Hilbert.GLPoint3.Kripke

instance finite_sound : Sound (Hilbert.GLPoint3) FrameClass.finite_strict_linear_order := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _⟩ _ (rfl | rfl);
  . exact validate_AxiomL_of_finite_trans_irrefl;
  . exact validate_WeakPoint3_of_weakConnected;

instance consistent : Entailment.Consistent (Hilbert.GLPoint3) :=
  consistent_of_sound_frameclass FrameClass.finite_strict_linear_order $ by
    use blackpoint;
    refine ⟨inferInstance, inferInstance, inferInstance⟩;

instance finite_complete : Complete (Hilbert.GLPoint3) (FrameClass.finite_strict_linear_order) := by sorry;

end Hilbert.GLPoint3.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma GLPoint3.Kripke.finite_strict_linear_order : Logic.GLPoint3 = FrameClass.finite_strict_linear_order.logic := eq_hilbert_logic_frameClass_logic

instance : ProperSublogic Logic.GL Logic.GLPoint3 := ⟨by
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
⟩

instance : ProperSublogic Logic.K4Point3 Logic.GLPoint3 := ⟨by
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
⟩

end Logic

end LO.Modal

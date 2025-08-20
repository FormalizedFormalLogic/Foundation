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
  p_connected := by tauto

end Kripke


namespace Hilbert.GLPoint3.Kripke

instance : Sound Hilbert.GLPoint3 FrameClass.finite_GLPoint3 := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates
  constructor
  rintro _ (rfl | rfl | rfl) F ⟨_, _⟩
  . exact validate_AxiomL_of_finite_trans_irrefl
  . exact validate_WeakPoint3_of_weakConnected

instance : Entailment.Consistent Hilbert.GLPoint3 :=
  consistent_of_sound_frameclass FrameClass.finite_GLPoint3 $ by
    use blackpoint
    constructor

instance : Complete Hilbert.GLPoint3 FrameClass.finite_GLPoint3 := by sorry


instance : Hilbert.GL ⪱ Hilbert.GLPoint3 := by
  constructor
  . apply Hilbert.Normal.weakerThan_of_provable_axioms
    rintro _ (rfl | rfl | rfl) <;> simp
  . apply Entailment.not_weakerThan_iff.mpr
    use (Axioms.WeakPoint3 (.atom 0) (.atom 1))
    constructor
    . simp
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.finite_GL)
      let M : Model := ⟨⟨Fin 3, λ x y => (x = 0 ∧ y = 1) ∨ (x = 0 ∧ y = 2)⟩, (λ w a => match a with | 0 => w = 1 | 1 => w = 2 | _ => False)⟩
      apply Kripke.not_validOnFrameClass_of_exists_model_world
      use M, 0
      constructor
      . apply Set.mem_setOf_eq.mpr
        exact {
          trans := by omega,
          irrefl := by omega
        }
      . suffices (0 : M.World) ≺ 1 ∧ (∀ x, (1 : M.World) ≺ x → x = 1) ∧ (0 : M.World) ≺ 2 ∧ ∀ x, (2 : M.World) ≺ x → x = 2 by
          simpa [Semantics.Realize, Satisfies, ValidOnFrame, M]
        refine ⟨?_, ?_, ?_, ?_⟩
        all_goals omega

instance : Hilbert.K4Point3 ⪱ Hilbert.GLPoint3 := by
  constructor
  . apply Hilbert.Normal.weakerThan_of_provable_axioms
    rintro _ (rfl | rfl | rfl) <;> simp
  . apply Entailment.not_weakerThan_iff.mpr
    use (Axioms.L (.atom 0))
    constructor
    . simp
    . apply Sound.not_provable_of_countermodel (𝓜 := Kripke.FrameClass.K4Point3)
      apply Kripke.not_validOnFrameClass_of_exists_model_world
      use ⟨⟨Fin 2, λ x y => x ≤ y⟩, (λ w a => False)⟩, 0
      constructor
      . apply Set.mem_setOf_eq.mpr
        constructor
      . simp [Semantics.Realize, Satisfies]
        constructor
        . intro y Rxy
          use y
        . use 1
          omega

end Hilbert.GLPoint3.Kripke

instance : Modal.GL ⪱ Modal.GLPoint3 := inferInstance

instance : Modal.K4Point3 ⪱ Modal.GLPoint3 := inferInstance

end LO.Modal

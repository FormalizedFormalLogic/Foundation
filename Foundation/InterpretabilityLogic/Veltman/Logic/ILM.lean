import Foundation.InterpretabilityLogic.Veltman.Logic.IL
import Foundation.InterpretabilityLogic.Veltman.AxiomM

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected class Frame.IsILM (F : Veltman.Frame) extends F.IsIL, F.HasAxiomM
protected abbrev FrameClass.ILM : FrameClass := { F | F.IsILM }

instance : trivialFrame.IsILM where
  S_M := by tauto

end Veltman


open Hilbert.Basic

namespace ILM

instance Veltman.sound : Sound InterpretabilityLogic.ILM FrameClass.ILM := by
  apply Veltman.instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.ILM := Veltman.consistent_of_sound_frameclass FrameClass.ILM $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end ILM

instance : InterpretabilityLogic.IL ⪱ InterpretabilityLogic.ILM := by
  constructor;
  . apply weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.M (.atom 0) (.atom 1) (.atom 2));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.IL);
      apply Veltman.not_validOnFrameClass_of_exists_frame;
      use {
        toKripkeFrame := {
          World := Fin 4
          Rel x y := (x = 0 ∧ 0 < y) ∨ (x = 2 ∧ y = 3)
        }
        isGL := Modal.Kripke.Frame.isGL_of_isFiniteGL {
          trans := by omega;
          irrefl := by omega;
        }
        S w x y :=
           (w = 0 ∧ 1 ≤ x ∧ x ≤ y) ∨
           (w = 2 ∧ x = 3 ∧ y = 3)
        S_cond := by grind;
      }
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        exact {
          S_J1 := by tauto;
          S_J2 := by grind;
          S_J4 := by
            rintro w x y (⟨rfl, h₁, h₂⟩ | ⟨rfl, rfl, rfl⟩);
            . left;
              constructor;
              . rfl;
              . simpa using Fin.le_trans h₁ h₂;
            . tauto;
          S_J5 := by
            rintro w x y (⟨rfl, h⟩ | ⟨rfl, rfl⟩) (⟨_, _⟩ | ⟨_, _⟩);
            . simp_all;
            . left; refine ⟨rfl, ?_, ?_⟩ <;> simp_all;
            . contradiction;
            . contradiction;
        }
      . by_contra hC;
        have := Veltman.Frame.HasAxiomM.of_validate_axiomM hC |>.S_M (w := 0) (x := 1) (y := 2) (z := 3) (by tauto) (by tauto);
        contradiction;

end LO.InterpretabilityLogic

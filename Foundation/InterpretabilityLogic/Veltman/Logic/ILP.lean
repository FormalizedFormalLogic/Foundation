import Foundation.InterpretabilityLogic.Veltman.Logic.IL
import Foundation.InterpretabilityLogic.Veltman.AxiomP

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected class Frame.IsILP (F : Veltman.Frame) extends F.IsIL, F.HasAxiomP
protected abbrev FrameClass.ILP : FrameClass := { F | F.IsILP }

instance : trivialFrame.IsILP where
  S_P := by tauto

end Veltman


open Hilbert.Basic

namespace ILP

instance Veltman.sound : Sound InterpretabilityLogic.ILP FrameClass.ILP := by
  apply Veltman.instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.ILP := Veltman.consistent_of_sound_frameclass FrameClass.ILP $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end ILP

instance : InterpretabilityLogic.IL ⪱ InterpretabilityLogic.ILP := by
  constructor;
  . apply weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.P (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.IL);
      apply Veltman.not_validOnFrameClass_of_exists_frame;
      use {
        toKripkeFrame := {
          World := Fin 4
          Rel x y := (x = 0 ∧ 0 < y) ∨ (x = 1 ∧ y = 2)
        }
        isGL := Modal.Kripke.Frame.isGL_of_isFiniteGL {
          trans := by omega;
          irrefl := by omega;
        }
        S w x y := (w = 0 ∧ 1 ≤ x ∧ x ≤ y) ∨ (w = 1 ∧ x = 2 ∧ y = 2)
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
        have := Veltman.Frame.HasAxiomP.of_validate_axiomP hC |>.S_P (w := 0) (x := 1) (y := 2) (z := 3) (by tauto) (by tauto);
        contradiction;

end LO.InterpretabilityLogic

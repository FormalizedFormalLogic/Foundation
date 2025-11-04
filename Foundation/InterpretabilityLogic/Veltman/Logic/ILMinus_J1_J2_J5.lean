import Foundation.InterpretabilityLogic.Veltman.Logic.ILMinus_J1_J4Plus_J5
import Foundation.InterpretabilityLogic.Veltman.Logic.ILMinus_J1_J2
import Foundation.InterpretabilityLogic.Veltman.Logic.ILMinus_J2Plus_J5

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected class Frame.IsILMinus_J1_J2_J5 (F : Veltman.Frame) extends F.HasAxiomJ1, F.HasAxiomJ2, F.HasAxiomJ5
protected abbrev FrameClass.ILMinus_J1_J2_J5 : FrameClass := { F | F.IsILMinus_J1_J2_J5 }

instance : trivialFrame.IsILMinus_J1_J2_J5 where

end Veltman


open Hilbert.Minimal

namespace ILMinus_J1_J2_J5

instance Veltman.sound : Sound InterpretabilityLogic.ILMinus_J1_J2_J5 FrameClass.ILMinus_J1_J2_J5 := by
  apply Veltman.instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases (by simpa [buildAxioms] using hφ) with (rfl | rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.ILMinus_J1_J2_J5 := Veltman.consistent_of_sound_frameclass FrameClass.ILMinus_J1_J2_J5 $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end ILMinus_J1_J2_J5


instance : InterpretabilityLogic.ILMinus_J1_J4Plus_J5 ⪱ InterpretabilityLogic.ILMinus_J1_J2_J5 := by
  constructor;
  . apply weakerThan_of_provable_axioms;
    intro φ hφ;
    rcases (by simpa [Hilbert.Minimal.buildAxioms] using hφ) with (rfl | rfl | rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.J2 (.atom 0) (.atom 1) (.atom 2));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.ILMinus_J1_J4Plus_J5);
      apply Veltman.not_validOnFrameClass_of_exists_frame;
      use {
        toKripkeFrame := {
          World := Fin 4
          Rel := λ x y => x = 0 ∧ (0 < y)
        }
        isGL := Modal.Kripke.Frame.isGL_of_isFiniteGL {
          trans := by tauto;
          irrefl := by omega;
        }
        S w x y := (w ≺ x ∧ x = y) ∨ (w = 0 ∧ 0 < x ∧ x < 3 ∧ y = x + 1),
        S_cond := by grind;
      };
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        exact {
          S_J1 := by grind;
          S_J4 := by
            simp only [Frame.SRel'];
            rintro w x y (h | ⟨rfl, h, h, rfl⟩);
            . grind;
            . constructor;
              . tauto;
              . apply Fin.add_one_pos; simpa;
          S_J5 := by grind;
        }
      . by_contra hC;
        have := Veltman.Frame.HasAxiomJ2.of_validate_axiomJ2 hC |>.S_J2 (w := 0) (x := 1) (y := 2) (z := 3) (by tauto) (by tauto);
        simp [Frame.SRel'] at this;

instance : InterpretabilityLogic.ILMinus_J2Plus_J5 ⪱ InterpretabilityLogic.ILMinus_J1_J2_J5 := by
  constructor;
  . apply weakerThan_of_provable_axioms;
    intro φ hφ;
    rcases (by simpa [Hilbert.Minimal.buildAxioms] using hφ) with (rfl | rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.J1 (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.ILMinus_J2Plus_J5);
      apply Veltman.not_validOnFrameClass_of_exists_frame;
      use {
        toKripkeFrame := ⟨Fin 2, (· < ·)⟩
        isGL := Modal.Kripke.Frame.isGL_of_isFiniteGL {
          trans := by omega;
          irrefl := by omega;
        }
        S w x y := False,
        S_cond := by tauto;
      }
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        exact {
          S_J2 := by grind,
          S_J4 := by grind,
          S_J5 := by grind,
        }
      . by_contra hC;
        have := Veltman.Frame.HasAxiomJ1.of_validate_axiomJ1 hC |>.S_J1 (w := 0) (x := 1) (by omega);
        contradiction;

instance : InterpretabilityLogic.ILMinus_J1_J2 ⪱ InterpretabilityLogic.ILMinus_J1_J2_J5 := by
  constructor;
  . apply weakerThan_of_subset_axioms $ by grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.J5 (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.ILMinus_J1_J2);
      apply Veltman.not_validOnFrameClass_of_exists_frame;
      use {
        toKripkeFrame := {
          World := Fin 3
          Rel := λ x y => x < y
        }
        isGL := Modal.Kripke.Frame.isGL_of_isFiniteGL {
          trans := by omega;
          irrefl := by omega;
        }
        S w x y := w ≺ x ∧ x = y
        S_cond := by omega;
      }
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        exact {
          S_J1 := by tauto;
          S_J2 := by grind;
          S_J4 := by grind;
        }
      . by_contra hC;
        replace hC := Veltman.Frame.HasAxiomJ5.of_validate_axiomJ5 hC |>.S_J5 (show 0 < 1 by omega) (show 1 < 2 by omega);
        contradiction

end LO.InterpretabilityLogic

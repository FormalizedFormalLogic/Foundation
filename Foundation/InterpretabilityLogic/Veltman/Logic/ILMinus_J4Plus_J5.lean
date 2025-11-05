import Foundation.InterpretabilityLogic.Veltman.Logic.ILMinus_J5
import Foundation.InterpretabilityLogic.Veltman.Logic.ILMinus_J4Plus

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected class Frame.IsILMinus_J4Plus_J5 (F : Veltman.Frame) extends F.HasAxiomJ4, F.HasAxiomJ5
protected abbrev FrameClass.ILMinus_J4Plus_J5 : FrameClass := { F | F.IsILMinus_J4Plus_J5 }

instance : trivialFrame.IsILMinus_J4Plus_J5 where

end Veltman


open Hilbert.Minimal

namespace ILMinus_J4Plus_J5

instance Veltman.sound : Sound InterpretabilityLogic.ILMinus_J4Plus_J5 FrameClass.ILMinus_J4Plus_J5 := by
  apply Veltman.instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases (by simpa [buildAxioms] using hφ) with (rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.ILMinus_J4Plus_J5 := Veltman.consistent_of_sound_frameclass FrameClass.ILMinus_J4Plus_J5 $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end ILMinus_J4Plus_J5


instance : InterpretabilityLogic.ILMinus_J4Plus ⪱ InterpretabilityLogic.ILMinus_J4Plus_J5 := by
  constructor;
  . apply weakerThan_of_subset_axioms $ by grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.J5 (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.ILMinus_J4Plus);
      apply Veltman.not_validOnFrameClass_of_exists_frame;
      use {
        toKripkeFrame := {
          World := Fin 4
          Rel := λ x y => x < y
        }
        isGL := Modal.Kripke.Frame.isGL_of_isFiniteGL {
          trans := by omega;
          irrefl := by omega;
        }
        S w x y := False,
        S_cond := by tauto;
      }
      constructor;
      . constructor; tauto;
      . by_contra hC;
        replace hC := Veltman.Frame.HasAxiomJ5.of_validate_axiomJ5 hC |>.S_J5 (show 0 < 1 by omega) (show 1 < 2 by omega);
        contradiction

instance : InterpretabilityLogic.ILMinus_J5 ⪱ InterpretabilityLogic.ILMinus_J4Plus_J5 := by
  constructor;
  . apply weakerThan_of_subset_axioms $ by grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.J4Plus (.atom 0) (.atom 1) (.atom 2));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.ILMinus_J5);
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
        S w x y := w ≺ x,
        S_cond := by omega
      }
      constructor;
      . constructor;
        intro w x y;
        omega;
      . by_contra hC;
        have := Veltman.Frame.HasAxiomJ4.of_validate_axiomJ4Plus hC |>.S_J4 (w := 1) (x := 2) (y := 0) (by omega);
        contradiction;

end LO.InterpretabilityLogic

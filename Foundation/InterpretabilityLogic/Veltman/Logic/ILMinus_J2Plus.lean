module
import Foundation.InterpretabilityLogic.Veltman.Logic.ILMinus_J4Plus
import Foundation.InterpretabilityLogic.Veltman.AxiomJ2


namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected abbrev FrameClass.ILMinus_J2Plus : FrameClass := { F | F.HasAxiomJ2 }

instance : trivialFrame.HasAxiomJ2 where
  S_J2 _ := by contradiction

end Veltman


open Hilbert.Minimal

namespace ILMinus_J2Plus

instance Veltman.sound : Sound InterpretabilityLogic.ILMinus_J2Plus FrameClass.ILMinus_J2Plus := by
  apply Veltman.instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases (by simpa [buildAxioms] using hφ) with (rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.ILMinus_J2Plus := Veltman.consistent_of_sound_frameclass FrameClass.ILMinus_J2Plus $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end ILMinus_J2Plus

instance : InterpretabilityLogic.ILMinus_J4Plus ⪱ InterpretabilityLogic.ILMinus_J2Plus := by
  constructor;
  . apply weakerThan_of_provable_axioms;
    intro φ hφ;
    rcases (by simpa [Hilbert.Minimal.buildAxioms] using hφ) with (rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.J2Plus (.atom 0) (.atom 1) (.atom 2));
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
        S w x y := w < x ∧ x < y ∧ (w = 0 ∧ ¬(x = 1 ∧ y = 3)),
        S_cond := by omega;
      }
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        constructor;
        simp;
        omega;
      . by_contra hC;
        have := Veltman.Frame.HasAxiomJ2.of_validate_axiomJ2Plus hC |>.S_J2 (w := 0) (x := 1) (y := 2) (z := 3) (by tauto) (by tauto);
        contradiction;

end LO.InterpretabilityLogic

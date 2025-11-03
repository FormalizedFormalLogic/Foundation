import Foundation.InterpretabilityLogic.Veltman.Logic.ILMinus
import Foundation.InterpretabilityLogic.Veltman.AxiomJ4


namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected abbrev FrameClass.ILMinus_J4Plus : FrameClass := { F | F.HasAxiomJ4 }

instance : trivialFrame.HasAxiomJ4 where
  S_J4 {w x y} Swxy := by have := x.2; contradiction;

end Veltman


open Hilbert.Minimal

namespace ILMinus_J4Plus

instance Veltman.sound : Sound InterpretabilityLogic.ILMinus_J4Plus FrameClass.ILMinus_J4Plus := by
  apply Veltman.instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases (by simpa [buildAxioms] using hφ) with (rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.ILMinus_J4Plus := Veltman.consistent_of_sound_frameclass FrameClass.ILMinus_J4Plus $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end ILMinus_J4Plus

instance : InterpretabilityLogic.ILMinus ⪱ InterpretabilityLogic.ILMinus_J4Plus := by
  constructor;
  . apply weakerThan_of_subset_axioms $ by grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.J4Plus (.atom 0) (.atom 1) (.atom 2));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.ILMinus);
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
        S _ _ _ := False
      }
      constructor;
      . tauto;
      . by_contra hC;
        replace hC : ¬1 < 2 := Veltman.Frame.HasAxiomJ4.of_validate_axiomJ4 hC |>.S_J4Plus 0 ⟨1, by omega⟩ ⟨2, by omega⟩;
        omega;

end LO.InterpretabilityLogic

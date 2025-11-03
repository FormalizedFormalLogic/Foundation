import Foundation.InterpretabilityLogic.Veltman.Logic.ILMinus
import Foundation.InterpretabilityLogic.Veltman.AxiomJ5


namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected abbrev FrameClass.ILMinus_J5 : FrameClass := { F | F.HasAxiomJ5 }

instance : trivialFrame.HasAxiomJ5 where
  S_J5 _ := by tauto

end Veltman


open Hilbert.Minimal

namespace ILMinus_J5

instance Veltman.sound : Sound InterpretabilityLogic.ILMinus_J5 FrameClass.ILMinus_J5 := by
  apply Veltman.instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases (by simpa [buildAxioms] using hφ) with (rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.ILMinus_J5 := Veltman.consistent_of_sound_frameclass FrameClass.ILMinus_J5 $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end ILMinus_J5

instance : InterpretabilityLogic.ILMinus ⪱ InterpretabilityLogic.ILMinus_J5 := by
  constructor;
  . apply weakerThan_of_subset_axioms $ by grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.J5 (.atom 0));
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
        replace hC : ¬1 < 2 := Veltman.Frame.HasAxiomJ5.of_validate_axiomJ5 hC |>.S_J5 0 ⟨1, by omega⟩ ⟨2, by omega⟩;
        omega;

end LO.InterpretabilityLogic

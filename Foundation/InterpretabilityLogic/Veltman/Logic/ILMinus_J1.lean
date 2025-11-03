import Foundation.InterpretabilityLogic.Veltman.Logic.ILMinus
import Foundation.InterpretabilityLogic.Veltman.AxiomJ1


namespace LO.Modal.Kripke

lemma Frame.isGL_of_isFiniteGL {F : Kripke.Frame} (hF : F.IsFiniteGL) : F.IsGL := by constructor;

end LO.Modal.Kripke



namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected abbrev FrameClass.ILMinus_J1 : FrameClass := { F | F.HasAxiomJ1 }

instance : trivialFrame.HasAxiomJ1 where
  S_refl _ := ⟨by tauto⟩

end Veltman


open Hilbert.Minimal

namespace ILMinus_J1

instance Veltman.sound : Sound InterpretabilityLogic.ILMinus_J1 FrameClass.ILMinus_J1 := by
  apply Veltman.instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases (by simpa [buildAxioms] using hφ) with (rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.ILMinus_J1 := Veltman.consistent_of_sound_frameclass FrameClass.ILMinus_J1 $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end ILMinus_J1

instance : InterpretabilityLogic.ILMinus ⪱ InterpretabilityLogic.ILMinus_J1 := by
  constructor;
  . apply weakerThan_of_subset_axioms $ by grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.J1 (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := Veltman.FrameClass.ILMinus);
      apply Veltman.not_validOnFrameClass_of_exists_frame;
      use {
        toKripkeFrame := {
          World := Fin 2
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
        replace hC := Veltman.Frame.HasAxiomJ1.of_validate_axiomJ1 hC |>.S_refl 0;
        have := @hC.refl ⟨1, by omega⟩
        simp at this;

end LO.InterpretabilityLogic

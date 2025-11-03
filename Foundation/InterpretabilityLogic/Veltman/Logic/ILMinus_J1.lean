import Foundation.InterpretabilityLogic.Veltman.Logic.ILMinus
import Foundation.InterpretabilityLogic.Veltman.AxiomJ1

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected abbrev FrameClass.ILMinus_J1 : FrameClass := { F | F.HasAxiomJ1 }

instance : trivialFrame.HasAxiomJ1 where
  S_refl _ := ⟨by tauto⟩

end Veltman


namespace ILMinus_J1

open Hilbert.Minimal

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

end LO.InterpretabilityLogic

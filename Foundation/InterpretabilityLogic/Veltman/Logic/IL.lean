import Foundation.InterpretabilityLogic.Veltman.Logic.ILMinus_J1_J2_J5
import Foundation.InterpretabilityLogic.Veltman.Logic.CL


namespace LO.InterpretabilityLogic

open Veltman

namespace Veltman

protected alias Frame.IsIL := Frame.IsILMinus_J1_J2_J5
protected alias FrameClass.IL := FrameClass.ILMinus_J1_J2_J5

end Veltman


namespace IL

instance Veltman.sound : Sound InterpretabilityLogic.IL FrameClass.IL := by
  constructor;
  intro φ hφ;
  apply ILMinus_J1_J2_J5.Veltman.sound.sound;
  apply Entailment.Equiv.iff.mp inferInstance _ |>.mp hφ;

instance : Entailment.Consistent InterpretabilityLogic.IL := by
  apply Entailment.Consistent.of_le  (𝓢 := InterpretabilityLogic.ILMinus_J1_J2_J5) <;>
  infer_instance;

end IL

end LO.InterpretabilityLogic

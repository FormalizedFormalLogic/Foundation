import Foundation.InterpretabilityLogic.Veltman.Logic.ILMinus_J1_J2
import Foundation.InterpretabilityLogic.Hilbert.Basic_Minimal


namespace LO.InterpretabilityLogic

open Veltman

namespace Veltman

protected alias Frame.IsCL := Frame.IsILMinus_J1_J2
protected alias FrameClass.CL := FrameClass.ILMinus_J1_J2

end Veltman


namespace CL

instance Veltman.sound : Sound InterpretabilityLogic.CL FrameClass.CL := by
  constructor;
  intro φ hφ;
  apply ILMinus_J1_J2.Veltman.sound.sound;
  apply Entailment.Equiv.iff.mp inferInstance _ |>.mp hφ;

instance : Entailment.Consistent InterpretabilityLogic.CL := by
  apply Entailment.Consistent.of_le  (𝓢 := InterpretabilityLogic.ILMinus_J1_J2) <;>
  infer_instance;

end CL

end LO.InterpretabilityLogic

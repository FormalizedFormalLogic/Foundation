import Foundation.InterpretabilityLogic.Veltman.Logic.IL_F

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected class Frame.IsIL_W (F : Veltman.Frame) extends F.IsIL, F.HasAxiomW
protected abbrev FrameClass.IL_W : FrameClass := { F | F.IsIL_W }

instance : trivialFrame.IsIL_W where

end Veltman


open Hilbert.Basic

namespace IL_W

instance Veltman.sound : Sound InterpretabilityLogic.IL_W FrameClass.IL_W := by
  apply Veltman.instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.IL_W := Veltman.consistent_of_sound_frameclass FrameClass.IL_W $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end IL_W

end LO.InterpretabilityLogic

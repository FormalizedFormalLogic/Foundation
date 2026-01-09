module
import Foundation.InterpretabilityLogic.Veltman.Logic.IL_P₀

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected class Frame.IsIL_R (F : Veltman.Frame) extends F.IsIL, F.HasAxiomR
protected abbrev FrameClass.IL_R : FrameClass := { F | F.IsIL_R }

instance : trivialFrame.IsIL_R where

end Veltman


open Hilbert.Basic

namespace IL_R

instance Veltman.sound : Sound InterpretabilityLogic.IL_R FrameClass.IL_R := by
  apply Veltman.instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.IL_R := Veltman.consistent_of_sound_frameclass FrameClass.IL_R $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end IL_R

end LO.InterpretabilityLogic

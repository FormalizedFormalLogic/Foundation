import Foundation.InterpretabilityLogic.Veltman.Logic.ILF

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected class Frame.IsILW (F : Veltman.Frame) extends F.IsIL, F.HasAxiomW
protected abbrev FrameClass.ILW : FrameClass := { F | F.IsILW }

instance : trivialFrame.IsILW where

end Veltman


open Hilbert.Basic

namespace ILW

instance Veltman.sound : Sound InterpretabilityLogic.ILW FrameClass.ILW := by
  apply Veltman.instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.ILW := Veltman.consistent_of_sound_frameclass FrameClass.ILW $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end ILW

end LO.InterpretabilityLogic

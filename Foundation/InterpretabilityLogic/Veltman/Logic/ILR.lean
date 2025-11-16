import Foundation.InterpretabilityLogic.Veltman.Logic.ILP₀

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected class Frame.IsILR (F : Veltman.Frame) extends F.IsIL, F.HasAxiomR
protected abbrev FrameClass.ILR : FrameClass := { F | F.IsILR }

instance : trivialFrame.IsILR where

end Veltman


open Hilbert.Basic

namespace ILR

instance Veltman.sound : Sound InterpretabilityLogic.ILR FrameClass.ILR := by
  apply Veltman.instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with (rfl | rfl | rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.ILR := Veltman.consistent_of_sound_frameclass FrameClass.ILR $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end ILR

end LO.InterpretabilityLogic

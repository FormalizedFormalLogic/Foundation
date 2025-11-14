import Foundation.InterpretabilityLogic.Veltman.Logic.ILP₀
import Foundation.InterpretabilityLogic.Veltman.Logic.ILW

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected class Frame.IsILRW (F : Veltman.Frame) extends F.IsIL, F.HasAxiomW, F.HasAxiomR
protected abbrev FrameClass.ILRW : FrameClass := { F | F.IsILRW }

instance : trivialFrame.IsILRW where

end Veltman


open Hilbert.Basic

namespace ILRW

instance Veltman.sound : Sound InterpretabilityLogic.ILRW FrameClass.ILRW := by
  apply Veltman.instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  simp only [Set.union_insert, Set.union_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hφ;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.ILRW := Veltman.consistent_of_sound_frameclass FrameClass.ILRW $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end ILRW

end LO.InterpretabilityLogic

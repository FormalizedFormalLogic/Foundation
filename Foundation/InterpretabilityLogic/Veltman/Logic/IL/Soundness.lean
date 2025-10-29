import Foundation.InterpretabilityLogic.Veltman.Logic.CL

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected abbrev FrameClass.IL : FrameClass := { F | F.IsIL }


protected class Frame.IsFiniteIL (F : Veltman.Frame) extends F.IsIL, F.IsFinite where

protected abbrev FrameClass.FiniteIL : FrameClass := { F | F.IsFiniteIL }


instance : Veltman.trivialFrame.IsIL where
  S_IL _ _ _ := by simp;

end Veltman


namespace IL

instance Veltman.sound : Sound InterpretabilityLogic.IL FrameClass.IL := instSound_of_validates_axioms $ by
  constructor;
  rintro φ (rfl | hφ) F hF;
  . simp only [Set.mem_setOf_eq] at hF;
    apply Formula.Veltman.ValidOnFrame.axiomJ5;
  . simp only [Set.mem_setOf_eq] at hF;
    apply validates_CL_axioms_union.models;
    assumption;

instance : Entailment.Consistent InterpretabilityLogic.IL := consistent_of_sound_frameclass FrameClass.IL $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end IL

end LO.InterpretabilityLogic

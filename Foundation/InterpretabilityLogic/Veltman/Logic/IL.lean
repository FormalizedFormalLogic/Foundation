import Foundation.InterpretabilityLogic.Veltman.Logic.CL

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected abbrev FrameClass.IL : FrameClass := { F | F.IsIL }

instance : Veltman.trivialFrame.IsIL where
  S_IL _ _ _ := by simp;

end Veltman


namespace IL

instance Veltman.sound : Sound InterpretabilityLogic.IL FrameClass.IL := by
  apply instSound_of_validates_axioms;
  . intro F hF;
    replace hF := Set.mem_setOf_eq.mp hF;
    infer_instance;
  . constructor;
    intro φ hφ F hF;
    replace hF := Set.mem_setOf_eq.mp hF;
    rcases hφ with (rfl | rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.IL := consistent_of_sound_frameclass FrameClass.IL $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end IL

end LO.InterpretabilityLogic

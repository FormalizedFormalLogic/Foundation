import Foundation.InterpretabilityLogic.Veltman.Logic.CL

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected abbrev FrameClass.IL : FrameClass := { F | F.IsIL }

instance : Veltman.trivialFrame.IsIL where
  S_IL _ _ _ := by simp;

end Veltman


namespace IL

instance Veltman.sound : Sound InterpretabilityLogic.IL FrameClass.IL := instSound_of_validates_axioms $ by
  rw [(show IL.axioms = CL.axioms ∪ {(InterpretabilityLogic.Axioms.J5 (.atom 0))} by simp)];
  apply validates_CL_axioms_union;
  constructor;
  suffices FrameClass.IL ⊧ Axioms.J5 (Formula.atom 0) by simpa;
  intro F hF;
  simp only [Set.mem_setOf_eq] at hF;
  apply Formula.Veltman.ValidOnFrame.axiomJ5;

instance : Entailment.Consistent InterpretabilityLogic.IL := consistent_of_sound_frameclass FrameClass.IL $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end IL

end LO.InterpretabilityLogic

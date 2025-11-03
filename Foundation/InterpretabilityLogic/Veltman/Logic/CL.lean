import Foundation.InterpretabilityLogic.Veltman.Hilbert

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected abbrev FrameClass.CL : FrameClass := { F | F.IsCL }

abbrev trivialFrame : Veltman.Frame where
  toKripkeFrame := Modal.Kripke.blackpoint
  S _ _ _ := True

instance : Veltman.trivialFrame.IsCL where
  S_refl _ := ⟨by tauto⟩
  S_trans _ := ⟨by tauto⟩

end Veltman


namespace CL

instance Veltman.sound : Sound InterpretabilityLogic.CL FrameClass.CL := by
  apply instSound_of_validates_axioms;
  . intro F hF;
    replace hF := Set.mem_setOf_eq.mp hF;
    infer_instance;
  . constructor;
    intro φ hφ F hF;
    replace hF := Set.mem_setOf_eq.mp hF;
    rcases hφ with (rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.CL := consistent_of_sound_frameclass FrameClass.CL $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end CL

end LO.InterpretabilityLogic

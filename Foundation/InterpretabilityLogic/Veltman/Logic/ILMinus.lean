module

public import Foundation.InterpretabilityLogic.Veltman.Hilbert


@[expose] public section

namespace LO.Modal.Kripke

lemma Frame.isGL_of_isFiniteGL {F : Kripke.Frame} (hF : F.IsFiniteGL) : F.IsGL := by constructor;

end LO.Modal.Kripke



namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected abbrev FrameClass.ILMinus : FrameClass := Set.univ

abbrev trivialFrame : Veltman.Frame where
  toKripkeFrame := Modal.Kripke.blackpoint
  S _ _ _ := False
  S_cond := by tauto

end Veltman


namespace ILMinus

open Hilbert.Minimal.Veltman

instance Veltman.sound : Sound InterpretabilityLogic.ILMinus FrameClass.ILMinus := by
  apply instFrameClassSound;
  constructor;
  intro φ hφ F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  rcases hφ with (rfl | rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent InterpretabilityLogic.ILMinus := consistent_of_sound_frameclass FrameClass.ILMinus $ by
  use Veltman.trivialFrame;
  apply Set.mem_setOf_eq.mpr;
  simp;

end ILMinus


end LO.InterpretabilityLogic
end

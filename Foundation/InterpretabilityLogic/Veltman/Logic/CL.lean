import Foundation.InterpretabilityLogic.Veltman.Hilbert

namespace LO.InterpretabilityLogic

open Veltman


namespace Veltman

protected abbrev FrameClass.CL : FrameClass := Set.univ

abbrev trivialFrame : Veltman.Frame where
  toKripkeFrame := Modal.Kripke.blackpoint
  S _ _ _ := True
  S_refl _ := ⟨by tauto⟩
  S_trans _ := ⟨by tauto⟩

end Veltman


namespace CL

instance Veltman.sound : Sound InterpretabilityLogic.CL FrameClass.CL := instSound_of_validates_axioms $ by
  constructor;
  intro φ hφ;
  have := (show CL.axioms ∪ ∅ = CL.axioms by simp) ▸ validates_CL_axioms_union (Ax := ∅) (C := FrameClass.CL) ⟨by tauto⟩;
  apply this.models;
  assumption;

instance : Entailment.Consistent InterpretabilityLogic.CL := consistent_of_sound_frameclass FrameClass.CL $ by
  use Veltman.trivialFrame;
  simp;

end CL

end LO.InterpretabilityLogic

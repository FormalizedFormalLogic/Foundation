module

public import Foundation.Modal.Kripke.Logic.K

@[expose] public section

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Modal.Kripke

namespace Kripke

protected abbrev Frame.IsKD := Frame.IsSerial

protected abbrev FrameClass.KD : FrameClass := { F | F.IsKD }

end Kripke


namespace Hilbert

namespace KD.Kripke

instance : Sound Modal.KD FrameClass.KD := instSound_of_validates_axioms $ by
  apply FrameClass.validates_with_AxiomK_of_validates;
  constructor;
  simp only [Set.mem_singleton_iff, forall_eq];
  rintro F F_serial φ;
  apply validate_AxiomD_of_serial (ser := F_serial);

instance : Entailment.Consistent Modal.KD :=
  consistent_of_sound_frameclass FrameClass.KD $ by
    use whitepoint;
    apply Set.mem_setOf_eq.mpr;
    infer_instance;

instance : Canonical Modal.KD FrameClass.KD := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance : Complete Modal.KD FrameClass.KD := inferInstance

end KD.Kripke

instance : Modal.K ⪱ Modal.KD := by
  constructor;
  . grind;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.D (.atom 0));
    constructor;
    . exact axiomD!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.K)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ _ w => False⟩, 0;
      constructor;
      . trivial;
      . simp [Semantics.Models, Satisfies];

end Hilbert


end LO.Modal
end

import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.Normal.Basic
import Foundation.Modal.Kripke.Logic.K

namespace LO.Modal

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

namespace Kripke

protected abbrev Frame.IsKD := Frame.IsSerial

protected abbrev FrameClass.KD : FrameClass := { F | F.IsKD }

end Kripke


namespace Hilbert

namespace KD.Kripke

instance : Sound Hilbert.KD FrameClass.KD :=
  instSound_of_validates_axioms $ by
    apply FrameClass.Validates.withAxiomK;
    rintro F F_serial φ rfl;
    apply validate_AxiomD_of_serial (ser := F_serial);

instance : Entailment.Consistent Hilbert.KD :=
  consistent_of_sound_frameclass FrameClass.KD $ by
    use whitepoint;
    apply Set.mem_setOf_eq.mpr;
    infer_instance;

instance : Canonical Hilbert.KD FrameClass.KD := ⟨by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;
⟩

instance : Complete Hilbert.KD FrameClass.KD := inferInstance

end KD.Kripke

instance : Hilbert.K ⪱ Hilbert.KD := by
  constructor;
  . apply Hilbert.Normal.weakerThan_of_subset_axioms $ by simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.D (.atom 0));
    constructor;
    . exact axiomD!;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.all)
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ w _ => False⟩, 0;
      constructor;
      . trivial;
      . simp [Semantics.Realize, Satisfies];

end Hilbert

instance : Modal.K ⪱ Modal.KD := inferInstance


end LO.Modal

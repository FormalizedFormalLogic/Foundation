import Foundation.Modal.Neighborhood.Logic.EM
import Foundation.Modal.Neighborhood.AxiomGeach

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

instance : Frame.simple_blackhole.IsReflexive := by
  constructor;
  intro X x;
  simp_all;

protected class Frame.IsEMT (F : Frame) extends F.IsMonotonic, F.IsReflexive
protected abbrev FrameClass.EMT : FrameClass := { F | F.IsEMT }

end Neighborhood


namespace Hilbert

namespace EMT.Neighborhood

instance : Sound Hilbert.EMT FrameClass.EMT := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl) F (rfl | rfl) <;> simp;

instance : Entailment.Consistent Hilbert.EMT := consistent_of_sound_frameclass FrameClass.EMT $ by
  use Frame.simple_blackhole;
  apply Set.mem_setOf_eq.mpr;
  constructor;

end EMT.Neighborhood

instance : Hilbert.EM ⪱ Hilbert.EMT := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.T (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EM);
      apply not_validOnFrameClass_of_exists_frame;
      use ⟨Fin 1, λ _ => Set.univ⟩;
      constructor;
      . exact ⟨by tauto⟩;
      . apply not_imp_not.mpr isReflexive_of_valid_axiomT;
        by_contra! hC;
        simpa [Frame.box] using @hC.refl ∅;

end Hilbert

instance : 𝐄𝐌 ⪱ 𝐄𝐌𝐓 := inferInstance

end LO.Modal

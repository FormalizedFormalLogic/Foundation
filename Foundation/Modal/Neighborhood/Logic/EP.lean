import Foundation.Modal.Neighborhood.AxiomC
import Foundation.Modal.Neighborhood.AxiomGeach
import Foundation.Modal.Neighborhood.AxiomP
import Foundation.Modal.Neighborhood.AxiomN
import Foundation.Modal.Neighborhood.Logic.E

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

instance : Frame.simple_blackhole.NotContainsEmpty := by
  constructor
  simp only [Set.mem_singleton_iff, forall_const]
  tauto_set


@[reducible] protected alias Frame.IsEP := Frame.NotContainsEmpty
protected abbrev FrameClass.EP : FrameClass := { F | F.IsEP }


end Neighborhood


namespace Hilbert

namespace EP.Neighborhood

instance : Sound Hilbert.EP FrameClass.EP := instSound_of_validates_axioms $ by
  simp only [Semantics.RealizeSet.singleton_iff]
  intro F hF
  replace hF := Set.mem_setOf_eq.mp hF
  simp

instance : Entailment.Consistent Hilbert.EP := consistent_of_sound_frameclass FrameClass.EP $ by
  use Frame.simple_blackhole
  simp only [Set.mem_setOf_eq]
  infer_instance

end EP.Neighborhood

instance : Hilbert.E ⪱ Hilbert.EP := by
  constructor
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms
    simp
  . apply Entailment.not_weakerThan_iff.mpr
    use (Axioms.P)
    constructor
    . simp
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E)
      apply not_validOnFrameClass_of_exists_frame
      use ⟨Fin 1, λ _ => {∅}⟩
      constructor
      . tauto
      . apply not_imp_not.mpr notContainsEmpty_of_valid_axiomP
        by_contra! hC
        simpa using hC.not_contains_empty

end Hilbert

instance : 𝐄 ⪱ 𝐄𝐏 := inferInstance

end LO.Modal

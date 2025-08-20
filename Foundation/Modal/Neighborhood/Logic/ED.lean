import Foundation.Modal.Neighborhood.AxiomC
import Foundation.Modal.Neighborhood.AxiomGeach
import Foundation.Modal.Neighborhood.AxiomM
import Foundation.Modal.Neighborhood.AxiomN
import Foundation.Modal.Neighborhood.Logic.E

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

instance : Frame.simple_blackhole.IsSerial := by
  constructor
  intro X x
  simp only [Frame.box, Set.mem_singleton_iff, Set.mem_setOf_eq, Frame.dia, Set.compl_univ_iff, Set.mem_compl_iff]
  tauto_set


@[reducible] protected alias Frame.IsED := Frame.IsSerial
protected abbrev FrameClass.ED : FrameClass := { F | F.IsED }


end Neighborhood


namespace Hilbert

namespace ED.Neighborhood

instance : Sound Hilbert.ED FrameClass.ED := instSound_of_validates_axioms $ by
  simp only [Semantics.RealizeSet.singleton_iff]
  intro F hF
  replace hF := Set.mem_setOf_eq.mp hF
  simp

instance : Entailment.Consistent Hilbert.ED := consistent_of_sound_frameclass FrameClass.ED $ by
  use Frame.simple_blackhole
  simp only [Set.mem_setOf_eq]
  infer_instance

end ED.Neighborhood

instance : Hilbert.E ⪱ Hilbert.ED := by
  constructor
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms
    simp
  . apply Entailment.not_weakerThan_iff.mpr
    use (Axioms.D (.atom 0))
    constructor
    . simp
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E)
      apply not_validOnFrameClass_of_exists_frame
      use ⟨Fin 2, λ w => match w with | 0 => {{0}} | 1 => Set.univ⟩
      constructor
      . tauto
      . apply not_imp_not.mpr isSerial_of_valid_axiomD
        by_contra! hC
        have := @hC.serial {1} 1
        simp [Frame.box, Frame.dia] at this


end Hilbert

instance : 𝐄 ⪱ 𝐄𝐃 := inferInstance

end LO.Modal

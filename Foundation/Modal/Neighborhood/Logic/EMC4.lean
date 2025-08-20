import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.AxiomGeach
import Foundation.Modal.Neighborhood.Logic.E4
import Foundation.Modal.Neighborhood.Logic.EMC

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsEMC4 (F : Frame) extends F.IsMonotonic, F.IsRegular, F.IsTransitive where
protected abbrev FrameClass.EMC4 : FrameClass := { F | F.IsEMC4 }

end Neighborhood


namespace Hilbert

namespace E4.Neighborhood

instance : Sound Hilbert.EMC4 FrameClass.EMC4 := instSound_of_validates_axioms $ by
  constructor
  rintro _ (rfl | rfl | rfl) F (rfl | rfl) <;> simp

instance : Entailment.Consistent Hilbert.EMC4 := consistent_of_sound_frameclass FrameClass.EMC4 $ by
  use Frame.simple_blackhole
  simp only [Set.mem_setOf_eq]
  constructor

instance : Complete Hilbert.EMC4 FrameClass.EMC4 := complete_of_canonical_frame FrameClass.EMC4 (maximalCanonicalFrame (Hilbert.EMC4)) $ by
  apply Set.mem_setOf_eq.mpr
  constructor

end E4.Neighborhood

instance : Hilbert.EMC ⪱ Hilbert.EMC4 := by
  constructor
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms
    simp
  . apply Entailment.not_weakerThan_iff.mpr
    use (Axioms.Four (.atom 0))
    constructor
    . simp
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EMC)
      apply not_validOnFrameClass_of_exists_frame
      use Frame.trivial_nontransitive
      constructor
      . constructor
      . simp

end Hilbert

instance : 𝐄 ⪱ 𝐄𝟒 := inferInstance

end LO.Modal

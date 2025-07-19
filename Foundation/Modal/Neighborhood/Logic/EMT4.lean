import Foundation.Modal.Neighborhood.Logic.EMT
import Foundation.Modal.Neighborhood.Logic.E4

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsEMT4 (F : Frame) extends F.IsMonotonic, F.IsReflexive, F.IsTransitive where
protected abbrev FrameClass.EMT4 : FrameClass := { F | F.IsEMT4 }

end Neighborhood


namespace Hilbert

namespace EMT4.Neighborhood

instance : Sound Hilbert.EMT4 FrameClass.EMT4 := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl | rfl) F (rfl | rfl) <;> simp;

instance : Entailment.Consistent Hilbert.EMT4 := consistent_of_sound_frameclass FrameClass.EMT4 $ by
  use Frame.simple_blackhole;
  apply Set.mem_setOf_eq.mpr;
  constructor;

instance : Complete Hilbert.EMT4 FrameClass.EMT4 := complete_of_canonical_frame FrameClass.EMT4 (supplementalMinimalCanonicalFrame (Hilbert.EMT4)) $ by
  apply Set.mem_setOf_eq.mpr;
  constructor;

end EMT4.Neighborhood

instance : Hilbert.EMT ⪱ Hilbert.EMT4 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Four (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EMT);
      apply not_validOnFrameClass_of_exists_frame;
      use Frame.trivial_nontransitive;
      constructor;
      . constructor;
      . simp;

end Hilbert

instance : 𝐄𝐌𝐓 ⪱ 𝐄𝐌𝐓𝟒 := inferInstance

end LO.Modal

import Foundation.Modal.Neighborhood.Logic.E4
import Foundation.Modal.Neighborhood.Logic.ET
import Foundation.Modal.Neighborhood.Logic.EN

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsEN4 (F : Frame) extends F.ContainsUnit, F.IsTransitive where
protected abbrev FrameClass.EN4 : FrameClass := { F | F.IsEN4 }

instance : counterframe_2_3_5.IsEN where
  contains_unit := by simp [Frame.box];

end Neighborhood


namespace EN4

instance : Sound Modal.EN4 FrameClass.EN4 := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl | rfl) F hF <;>
  . have := Set.mem_setOf_eq.mp hF;
    simp;

instance : Entailment.Consistent Modal.EN4 := consistent_of_sound_frameclass FrameClass.EN4 $ by
  use Frame.simple_blackhole;
  apply Set.mem_setOf_eq.mpr;
  constructor;

end EN4

instance : Modal.EN ⪱ Modal.EN4 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Four (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EN);
      apply not_validOnFrameClass_of_exists_frame;
      use counterframe_2_3_5;
      constructor;
      . apply Set.mem_setOf_eq.mpr; infer_instance;
      . simp;

instance : Modal.E4 ⪱ Modal.EN4 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.N;
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E4);
      apply not_validOnFrameClass_of_exists_frame;
      use Frame.simple_whitehole;
      constructor;
      . constructor;
        simp [Frame.box]
      . simp;

end LO.Modal

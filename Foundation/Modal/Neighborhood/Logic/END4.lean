import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.Logic.END
import Foundation.Modal.Neighborhood.Logic.E4

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsEND4 (F : Frame) extends F.IsEND, F.IsTransitive where
protected abbrev FrameClass.END4 : FrameClass := { F | F.IsEND4 }

end Neighborhood


namespace END4

instance : Sound Modal.END4 FrameClass.END4 := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl | rfl) F ⟨⟩ <;> simp;

instance : Entailment.Consistent Modal.END4 := consistent_of_sound_frameclass FrameClass.END4 $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  exact {}

end END4

instance : Modal.END ⪱ Modal.END4 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Four (.atom 0));
    constructor;
    . simp;
    . sorry;

end LO.Modal

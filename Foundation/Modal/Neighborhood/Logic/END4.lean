import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.Logic.END
import Foundation.Modal.Neighborhood.Logic.E4
import Foundation.Modal.Neighborhood.Logic.EN4
import Foundation.Vorspiel.Set.Fin

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsEND4 (F : Frame) extends F.IsEND, F.IsTransitive where
protected abbrev FrameClass.END4 : FrameClass := { F | F.IsEND4 }

instance : counterframe_2_3_5.IsEND where
  serial := by
    rintro X x;
    suffices X = {x}ᶜ ∨ X = Set.univ → ¬X = {x} ∧ ¬X = ∅ by simpa [Frame.box, Frame.dia];
    rintro (rfl | rfl) <;> simp [Set.Fin2.ne_singleton_univ.symm];

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
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.END);
      apply not_validOnFrameClass_of_exists_frame;
      use counterframe_2_3_5;
      constructor;
      . apply Set.mem_setOf_eq.mpr; infer_instance;
      . simp;

end LO.Modal

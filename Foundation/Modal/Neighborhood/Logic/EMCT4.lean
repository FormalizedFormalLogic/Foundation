import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.Logic.EMC4
import Foundation.Modal.Neighborhood.Logic.EMT4

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsEMCT4 (F : Frame) extends F.IsMonotonic, F.IsRegular, F.IsReflexive, F.IsTransitive where
protected abbrev FrameClass.EMCT4 : FrameClass := { F | F.IsEMCT4 }

instance : Frame.simple_blackhole.IsEMCT4 where

instance : Frame.simple_whitehole.IsEMCT4 where
  refl := by simp_all [Frame.simple_whitehole, Frame.box];
  trans := by simp_all [Frame.simple_whitehole, Frame.box];

end Neighborhood


namespace EMCT4

instance : Sound Modal.EMCT4 FrameClass.EMCT4 := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl | rfl | rfl) F ⟨_, _⟩ <;> simp;

instance : Entailment.Consistent Modal.EMCT4 := consistent_of_sound_frameclass FrameClass.EMCT4 $ by
  use Frame.simple_blackhole;
  constructor;

instance : Complete Modal.EMCT4 FrameClass.EMCT4 := maximalCanonicalFrame.completeness $ by
  apply Set.mem_setOf_eq.mpr;
  constructor;

end EMCT4

instance : Modal.EMCT4 ⪱ Modal.EMCNT4 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.N;
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EMCT4);
      apply not_validOnFrameClass_of_exists_frame;
      use Frame.simple_whitehole;
      constructor;
      . tauto;
      . simp;

end LO.Modal

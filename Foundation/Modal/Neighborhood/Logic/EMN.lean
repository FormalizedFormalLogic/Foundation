import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.Logic.EN
import Foundation.Modal.Neighborhood.Logic.EM



namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsEMN (F : Frame) extends F.IsMonotonic, F.ContainsUnit where
protected abbrev FrameClass.EMN : FrameClass := { F | F.IsEMN }

instance : counterframe_axiomC₁.IsEMN where
  contains_unit := by
    ext e;
    match e with | 0 | 1 => simp_all [counterframe_axiomC₁, Set.Fin2.eq_univ];

end Neighborhood


namespace EMN

instance : Sound Modal.EMN FrameClass.EMN := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl) F (rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent Modal.EMN := consistent_of_sound_frameclass FrameClass.EMN $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  constructor;

instance : Complete Modal.EMN FrameClass.EMN := (supplementedMinimalCanonicity Modal.EMN).completeness $ by
  apply Set.mem_setOf_eq.mpr;
  constructor;

end EMN

instance : Modal.EMN ⪱ Modal.EMCN := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.C (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EMN);
      apply not_validOnFrameClass_of_exists_frame;
      use counterframe_axiomC₁;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        infer_instance;
      . simp;

end LO.Modal

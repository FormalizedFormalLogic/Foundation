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

protected class Frame.IsEMT (F : Frame) extends F.IsMonotonic, F.IsReflexive where
protected abbrev FrameClass.EMT : FrameClass := { F | F.IsEMT }

end Neighborhood


namespace EMT

instance : Sound Modal.EMT FrameClass.EMT := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl) F (rfl | rfl) <;> simp;

instance : Entailment.Consistent Modal.EMT := consistent_of_sound_frameclass FrameClass.EMT $ by
  use Frame.simple_blackhole;
  apply Set.mem_setOf_eq.mpr;
  constructor;

instance : Complete Modal.EMT FrameClass.EMT := maximalCanonicalFrame.completeness $ by
  apply Set.mem_setOf_eq.mpr;
  constructor;

end EMT


instance : Modal.EMT ⪱ Modal.EMT4 := by
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

end LO.Modal

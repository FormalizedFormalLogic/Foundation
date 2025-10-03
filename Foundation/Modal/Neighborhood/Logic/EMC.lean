import Foundation.Modal.Neighborhood.AxiomGeach
import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.Logic.E4
import Foundation.Modal.Neighborhood.Logic.EC
import Foundation.Modal.Neighborhood.Logic.EM
import Foundation.Vorspiel.Set.Fin


namespace LO.Modal

open Formula (atom)
open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsEMC (F) extends Frame.IsMonotonic F, Frame.IsRegular F where
protected abbrev FrameClass.EMC : FrameClass := { F | F.IsEMC }

instance : Frame.simple_whitehole.IsEMC where
  regular := by simp_all [Frame.simple_whitehole, Frame.box];

end Neighborhood


namespace EMC

instance : Sound Modal.EMC FrameClass.EMC := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl) F (rfl | rfl) <;> simp;

instance : Entailment.Consistent Modal.EMC := consistent_of_sound_frameclass FrameClass.EMC $ by
  use Frame.simple_blackhole;
  simp;
  constructor;

instance : Complete Modal.EMC FrameClass.EMC := (maximalCanonicity Modal.EMC).completeness $ by
  apply Set.mem_setOf_eq.mpr;
  constructor;

end EMC

instance : Modal.EMC ⪱ Modal.EMCN := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.N;
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EMC);
      apply not_validOnFrameClass_of_exists_frame;
      use Frame.simple_whitehole;
      constructor;
      . tauto;
      . simp;

instance : Modal.EMC ⪱ Modal.EMC4 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Four (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EMC);
      apply not_validOnFrameClass_of_exists_frame;
      use Frame.trivial_nontransitive;
      constructor;
      . constructor;
      . simp;

end LO.Modal

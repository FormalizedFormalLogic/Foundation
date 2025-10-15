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
  constructor;
  intro X x;
  simp only [Frame.box, Set.mem_singleton_iff, Set.mem_setOf_eq, Frame.dia, Set.compl_univ_iff, Set.mem_compl_iff];
  tauto_set;

@[reducible] protected alias Frame.IsED := Frame.IsSerial
protected abbrev FrameClass.ED : FrameClass := { F | F.IsED }

instance : Frame.simple_whitehole.IsED where
  serial := by simp_all [Frame.simple_whitehole, Frame.box];

end Neighborhood


namespace ED

instance Neighborhood.sound : Sound Modal.ED FrameClass.ED := instSound_of_validates_axioms $ by
  simp only [Semantics.RealizeSet.singleton_iff];
  intro F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  simp;

instance consistent : Entailment.Consistent Modal.ED := consistent_of_sound_frameclass FrameClass.ED $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  infer_instance;

end ED

instance : Modal.ED ⪱ Modal.END := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.N;
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.ED);
      apply not_validOnFrameClass_of_exists_frame;
      use Frame.simple_whitehole;
      constructor;
      . apply Set.mem_setOf_eq.mpr; infer_instance;
      . simp;

end LO.Modal

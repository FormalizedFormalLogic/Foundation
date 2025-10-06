import Foundation.Modal.Neighborhood.AxiomGeach
import Foundation.Modal.Neighborhood.AxiomM
import Foundation.Modal.Neighborhood.AxiomC
import Foundation.Modal.Neighborhood.AxiomB
import Foundation.Modal.Neighborhood.Logic.E
import Foundation.Modal.Neighborhood.Filtration

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood


@[reducible] protected alias Frame.IsE5 := Frame.IsEuclidean
protected class Frame.IsFiniteE5 (F : Frame) extends F.IsE5, F.IsFinite

protected abbrev FrameClass.E5 : FrameClass := { F | F.IsE5 }
protected abbrev FrameClass.finite_E5 : FrameClass := { F | F.IsFiniteE5 }

instance : Frame.simple_blackhole.IsEuclidean := by
  constructor;
  intro X x hx;
  simp_all [(show X ≠ ∅ by grind), Frame.box];

end Neighborhood

namespace E5

instance : Sound Modal.E5 FrameClass.E5 := instSound_of_validates_axioms $ by
  simp only [Semantics.RealizeSet.singleton_iff];
  intro F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply valid_axiomFive_of_isEuclidean;

instance : Entailment.Consistent Modal.E5 := consistent_of_sound_frameclass FrameClass.E5 $ by
  use Frame.simple_blackhole;
  apply Set.mem_setOf_eq.mpr;
  infer_instance

instance : Complete Modal.E5 FrameClass.E5 := (maximalCanonicity _).completeness $ by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end E5

instance : Modal.E ⪱ Modal.E5 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Five (.atom 0));
    sorry;

end LO.Modal

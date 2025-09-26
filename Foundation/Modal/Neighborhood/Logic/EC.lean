import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.AxiomC
import Foundation.Modal.Neighborhood.Logic.E
import Foundation.Modal.Neighborhood.Supplementation

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

@[reducible] protected alias Frame.IsEC := Frame.IsRegular
protected abbrev FrameClass.EC : FrameClass := { F | F.IsEC }

end Neighborhood

instance : Sound Modal.EC FrameClass.EC := instSound_of_validates_axioms $ by
  constructor;
  rintro _ rfl F hF;
  simp_all;

instance : Entailment.Consistent Modal.EC := consistent_of_sound_frameclass FrameClass.EC $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  infer_instance;

instance : Complete Modal.EC FrameClass.EC := minimalCanonicalFrame.completeness $ by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

instance : Modal.E ⪱ Modal.EC := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.C (.atom 0) (.atom 1);
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E);
      apply not_validOnFrameClass_of_exists_model_world;
      let M : Model := {
        World := Fin 2,
        𝒩 := λ w =>
          match w with
          | 0 => {{0}, {1}}
          | 1 => {∅},
        Val := λ w =>
          match w with
          | 0 => {0}
          | 1 => {1}
          | _ => Set.univ
      };
      use M, 0;
      constructor;
      . tauto;
      . simp [M, Semantics.Realize, Satisfies]



end LO.Modal

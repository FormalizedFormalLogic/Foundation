import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.AxiomC
import Foundation.Modal.Neighborhood.Logic.E

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

@[reducible] protected alias Frame.IsEC := Frame.IsRegular
protected abbrev FrameClass.EC : FrameClass := { F | F.IsEC }

end Neighborhood


namespace Hilbert

namespace EC.Neighborhood

instance : Sound Hilbert.EC FrameClass.EC := instSound_of_validates_axioms $ by
  simp only [Semantics.RealizeSet.singleton_iff];
  intro F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply valid_axiomC_of_isRegular;

instance : Entailment.Consistent Hilbert.EC := consistent_of_sound_frameclass FrameClass.EC $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  infer_instance;

end EC.Neighborhood

instance : Hilbert.E ⪱ Hilbert.EC := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.C (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E);
      apply not_validOnFrameClass_of_exists_model_world;
      let M : Model := {
        World := Fin 2,
        N := λ w =>
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

end Hilbert

instance : 𝐄 ⪱ 𝐄𝐂 := inferInstance

end LO.Modal

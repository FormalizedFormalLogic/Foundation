import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.AxiomN
import Foundation.Modal.Neighborhood.Logic.E

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

@[reducible] protected alias Frame.IsEN := Frame.ContainsUnit
protected abbrev FrameClass.EN : FrameClass := { F | F.IsEN }

end Neighborhood


namespace Hilbert

namespace EN.Neighborhood

instance : Sound Hilbert.EN FrameClass.EN := instSound_of_validates_axioms $ by
  simp only [Semantics.RealizeSet.singleton_iff];
  intro F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply valid_axiomN_of_ContainsUnit;

instance : Entailment.Consistent Hilbert.EN := consistent_of_sound_frameclass FrameClass.EN $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  infer_instance;

end EN.Neighborhood

instance : Hilbert.E ⪱ Hilbert.EN := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.N;
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E);
      apply not_validOnFrameClass_of_exists_model_world;
      let M : Model := {
        World := Fin 1,
        ν := λ w => ∅,
        Val := λ w => Set.univ
      };
      use M, 0;
      constructor;
      . tauto;
      . simp! [M, Semantics.Realize, Satisfies];

end Hilbert

instance : 𝐄 ⪱ 𝐄𝐍 := inferInstance

end LO.Modal

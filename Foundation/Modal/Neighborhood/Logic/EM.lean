import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.AxiomM
import Foundation.Modal.Neighborhood.Logic.E

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

@[reducible] protected alias Frame.IsEM := Frame.IsMonotonic
protected abbrev FrameClass.EM : FrameClass := { F | F.IsEM }

end Neighborhood


namespace Hilbert

namespace EM.Neighborhood

instance : Sound Hilbert.EM FrameClass.EM := instSound_of_validates_axioms $ by
  simp only [Semantics.RealizeSet.singleton_iff];
  intro F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply valid_axiomM_of_isMonotonic;

instance : Entailment.Consistent Hilbert.EM := consistent_of_sound_frameclass FrameClass.EM $ by
  use Frame.trivial;
  simp only [Set.mem_setOf_eq];
  infer_instance;

end EM.Neighborhood

instance : Hilbert.E ⪱ Hilbert.EM := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.M (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E);
      apply not_validOnFrameClass_of_exists_model_world;
      let M : Model := {
        World := Fin 3,
        ν := λ w =>
          match w with
          | 0 => {{1}}
          | 1 => {{0}, {0, 1}}
          | 2 => {{0}, {1, 2}},
        Val := λ w =>
          match w with
          | 0 => {0, 1}
          | 1 => {1, 2}
          | _ => Set.univ
      };
      use M, 0;
      constructor;
      . tauto;
      . simp! [M, Semantics.Realize, Satisfies];
        ext x;
        simp;
        omega;

end Hilbert

instance : 𝐄 ⪱ 𝐄𝐌 := inferInstance

end LO.Modal

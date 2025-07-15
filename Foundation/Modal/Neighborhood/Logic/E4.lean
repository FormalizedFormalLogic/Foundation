import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.AxiomGeach
import Foundation.Modal.Neighborhood.Logic.E

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

instance : Frame.simple_blackhole.IsTransitive := by
  constructor;
  simp [Frame.box, Frame.box_iterate];

@[reducible] protected alias Frame.IsE4 := Frame.IsTransitive
protected abbrev FrameClass.E4 : FrameClass := { F | F.IsE4 }

end Neighborhood


namespace Hilbert

namespace E4.Neighborhood

instance : Sound Hilbert.E4 FrameClass.E4 := instSound_of_validates_axioms $ by
  simp only [Semantics.RealizeSet.singleton_iff];
  intro F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply valid_axiomFour_of_isTransitive;

instance : Entailment.Consistent Hilbert.E4 := consistent_of_sound_frameclass FrameClass.E4 $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  infer_instance;

end E4.Neighborhood

instance : Hilbert.E ⪱ Hilbert.E4 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Four (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E);
      apply not_validOnFrameClass_of_exists_frame;
      use {
        World := Fin 2,
        𝒩 w :=
          match w with
          | 0 => ∅
          | 1 => {{0, 1}},
      };
      constructor;
      . tauto;
      . apply not_imp_not.mpr isTransitive_of_valid_axiomFour;
        by_contra hC;
        have := @(hC.trans {0, 1});
        have := @this 1 ?_;
        . have := Set.Subset.antisymm_iff.mp this |>.2;
          have := @this 0;
          simp at this;
        . simp [Frame.box]

end Hilbert

instance : 𝐄 ⪱ 𝐄𝟒 := inferInstance

end LO.Modal

import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.AxiomGeach
import Foundation.Modal.Neighborhood.Logic.E4
import Foundation.Modal.Neighborhood.Logic.EMC

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsEMC4 (F : Frame) extends F.IsMonotonic, F.IsRegular, F.IsTransitive
protected abbrev FrameClass.EMC4 : FrameClass := { F | F.IsEMC4 }

end Neighborhood


namespace Hilbert

namespace E4.Neighborhood

instance : Sound Hilbert.EMC4 FrameClass.EMC4 := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl | rfl) F (rfl | rfl) <;> simp;

instance : Entailment.Consistent Hilbert.EMC4 := consistent_of_sound_frameclass FrameClass.EMC4 $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  constructor;

end E4.Neighborhood

instance : Hilbert.EMC ⪱ Hilbert.EMC4 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Four (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EMC);
      apply not_validOnFrameClass_of_exists_frame;
      use {
        World := Fin 2,
        𝒩 w :=
          match w with
          | 0 => ∅
          | 1 => {{0, 1}},
      };
      constructor;
      . exact {
          regular := by
            rintro X Y x ⟨hx, hy⟩;
            match x with
            | 0 => simp_all;
            | 1 => simp_all;
          mono := by
            rintro X Y x;
            match x with
            | 0 => simp_all;
            | 1 => sorry;
        }
      . apply not_imp_not.mpr isTransitive_of_valid_axiomFour;
        by_contra hC;
        have := @(hC.trans {0, 1});
        have := @this 1 ?_;
        . have := Set.Subset.antisymm_iff.mp this |>.2;
          have := @this 0;
          simp at this;
        . simp [Frame.box]

instance : Hilbert.E4 ⪱ Hilbert.EMC4 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.M (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E4);
      apply not_validOnFrameClass_of_exists_frame;
      use {
        World := Fin 2,
        𝒩 w :=
          match w with
          | 0 => ∅
          | 1 => {{0, 1}},
      };
      constructor;
      . sorry;
      . sorry;

end Hilbert

instance : 𝐄 ⪱ 𝐄𝟒 := inferInstance

end LO.Modal

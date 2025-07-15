import Foundation.Modal.Neighborhood.Logic.EMT
import Foundation.Modal.Neighborhood.Logic.E4

@[simp]
lemma Set.inter_eq_univ {s t : Set α} : s ∩ t = Set.univ ↔ s = Set.univ ∧ t = Set.univ := by
  simpa using @Set.sInter_eq_univ _ {s, t};

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsEMT4 (F : Frame) extends F.IsMonotonic, F.IsReflexive, F.IsTransitive
protected abbrev FrameClass.EMT4 : FrameClass := { F | F.IsEMT4 }

end Neighborhood


namespace Hilbert

namespace EMT4.Neighborhood

instance : Sound Hilbert.EMT4 FrameClass.EMT4 := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl | rfl) F (rfl | rfl) <;> simp;

instance : Entailment.Consistent Hilbert.EMT4 := consistent_of_sound_frameclass FrameClass.EMT4 $ by
  use Frame.simple_blackhole;
  apply Set.mem_setOf_eq.mpr;
  constructor;

end EMT4.Neighborhood

instance : Hilbert.EMT ⪱ Hilbert.EMT4 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Four (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EMT);
      apply not_validOnFrameClass_of_exists_frame;
      use ⟨
        Fin 2,
        λ w => match w with | 0 => ∅ | 1 => {Set.univ},
      ⟩;
      constructor;
      . exact {
          mono := by rintro X Y x; match x with | 0 | 1 => simp;
          refl := by rintro X x; match x with | 0 | 1 => first | tauto_set | simp_all;
        };
      . apply not_imp_not.mpr isTransitive_of_valid_axiomFour;
        by_contra! hC;
        have := (@hC.trans Set.univ);
        have := @this 1 ?_;
        . have := Set.Subset.antisymm_iff.mp this |>.2;
          simpa using @this 0;
        . simp;

end Hilbert

instance : 𝐄𝐌𝐓 ⪱ 𝐄𝐌𝐓𝟒 := inferInstance

end LO.Modal

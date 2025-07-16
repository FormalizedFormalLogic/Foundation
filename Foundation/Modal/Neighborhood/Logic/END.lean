import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.Logic.Incomparability.ED_EP

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsEND (F : Frame) extends F.ContainsUnit, F.IsSerial where
protected abbrev FrameClass.END : FrameClass := { F | F.IsEND }

end Neighborhood


namespace Hilbert

namespace END.Neighborhood

instance : Sound Hilbert.END FrameClass.END := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl) F (rfl | rfl) <;> simp;

instance : Entailment.Consistent Hilbert.END := consistent_of_sound_frameclass FrameClass.END $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  constructor;

end END.Neighborhood

instance : Hilbert.ED ⪱ Hilbert.END := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.N;
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.ED);
      apply not_validOnFrameClass_of_exists_frame;
      use {
        World := Fin 1,
        𝒩 := λ w => ∅,
      };
      constructor;
      . constructor;
        intro X x;
        simp [Frame.box, Frame.dia];
      . apply not_imp_not.mpr containsUnit_of_valid_axiomN;
        by_contra! hC;
        simpa using @hC.contains_unit 0;

instance : Hilbert.EP ⪱ Hilbert.END := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_provable_axioms;
    rintro _ rfl;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.D (.atom 0);
    constructor;
    . simp;
    . exact EP.unprovable_AxiomD;

end Hilbert

instance : 𝐄𝐃 ⪱ 𝐄𝐍𝐃 := inferInstance
instance : 𝐄𝐏 ⪱ 𝐄𝐍𝐃 := inferInstance

end LO.Modal

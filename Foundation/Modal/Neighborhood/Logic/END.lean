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




instance : Sound Modal.END FrameClass.END := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl) F (rfl | rfl) <;> simp;

instance : Entailment.Consistent Modal.END := consistent_of_sound_frameclass FrameClass.END $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  constructor;

instance : Modal.EP ⪱ Modal.END := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_provable_axioms;
    rintro _ rfl;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.D (.atom 0);
    constructor;
    . simp;
    . exact EP.unprovable_AxiomD;


end LO.Modal

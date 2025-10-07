import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.Logic.ECN
import Foundation.Modal.Neighborhood.Logic.EMC
import Foundation.Modal.Neighborhood.Logic.EMN


namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsEMCN (F : Frame) extends F.IsRegular, F.IsMonotonic, F.ContainsUnit where
protected abbrev FrameClass.EMCN : FrameClass := { F | F.IsEMCN }

end Neighborhood


namespace EMCN

instance : Sound Modal.EMCN FrameClass.EMCN := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl | rfl) F (rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent Modal.EMCN := consistent_of_sound_frameclass FrameClass.EMCN $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  constructor;

instance : Complete Modal.EMCN FrameClass.EMCN := (supplementedMinimalCanonicity Modal.EMCN).completeness $ by
  apply Set.mem_setOf_eq.mpr;
  constructor;

end EMCN


end LO.Modal

import Foundation.Modal.Neighborhood.Logic.EM
import Foundation.Modal.Neighborhood.Logic.EK


namespace LO.Modal

open Formula (atom)
open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood


namespace Neighborhood

protected class Frame.IsEMK (F : Frame) extends F.IsMonotonic, F.HasPropertyK where
protected abbrev FrameClass.EMK : FrameClass := { F | F.IsEMK }

instance : Frame.simple_blackhole.IsEMK where

end Neighborhood


namespace EMK

instance Neighborhood.sound : Sound Modal.EMK FrameClass.EMK := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl) F (rfl | rfl) <;> simp_all;

instance consistent : Entailment.Consistent Modal.EMK := consistent_of_sound_frameclass FrameClass.EMK $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  infer_instance;

end EMK


instance : Modal.EK ⪱ Modal.EMK := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_provable_axioms;
    rintro φ rfl; simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.M ((atom 0) ⋎ (atom 1)) (atom 1));
    constructor;
    . simp;
    . apply not_imp_not.mpr $ soundness_of_axioms_validOnFrame (F := EK_counterframe_for_M_and_C) ?_ <;> simp;

end LO.Modal

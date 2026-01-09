module
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
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms; simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.M ((atom 0) ⋎ (atom 1)) (atom 1));
    constructor;
    . simp;
    . apply not_imp_not.mpr $ soundness_of_axioms_validOnFrame (F := EK_counterframe_for_M_and_C) ?_ <;> simp;

instance : Modal.EM ⪱ Modal.EMCK := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms; simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.C (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EM);
      apply not_validOnFrameClass_of_exists_frame;
      use counterframe_axiomC₁;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        infer_instance;
      . simp;

instance : Modal.EM ⪱ Modal.EMK := calc
  _ ⪱ Modal.EMCK := inferInstance
  _ ≊ Modal.EMK  := by symm; infer_instance;

end LO.Modal

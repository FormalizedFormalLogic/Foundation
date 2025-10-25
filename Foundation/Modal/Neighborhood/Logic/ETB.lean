import Foundation.Modal.Neighborhood.Logic.EB
import Foundation.Modal.Neighborhood.Logic.ET

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsETB (F : Frame) extends F.IsReflexive, F.IsSymmetric
protected class Frame.IsFiniteETB (F : Frame) extends F.IsETB, F.IsFinite

protected abbrev FrameClass.ETB : FrameClass := { F | F.IsETB }
protected abbrev FrameClass.finite_ETB : FrameClass := { F | F.IsFiniteETB }

end Neighborhood



namespace ETB

instance Neighborhood.sound : Sound Modal.ETB FrameClass.ETB := instSound_of_validates_axioms $ by
  constructor;
  rintro φ (rfl | rfl) F hF <;>
  . replace hF := Set.mem_setOf_eq.mp hF; simp;

instance consistent : Entailment.Consistent Modal.ETB := consistent_of_sound_frameclass FrameClass.ETB $ by
  use Frame.simple_blackhole;
  constructor;

end ETB

instance : Modal.ET ⪱ Modal.ETB := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.B (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.ET);
      apply not_validOnFrameClass_of_exists_frame;
      use ⟨Fin 1, λ _ => ∅⟩;
      constructor;
      . constructor;
        simp [Frame.box]
      . by_contra! hC;
        have := isSymmetric_of_valid_axiomB hC |>.symm Set.univ;
        simp [Frame.box, Frame.dia] at this;

instance : Modal.EB ⪱ Modal.ETB := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.T (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EB);
      apply not_validOnFrameClass_of_exists_frame;
      use ⟨Fin 1, λ _ => Set.univ⟩;
      constructor;
      . tauto;
      . apply not_imp_not.mpr isReflexive_of_valid_axiomT;
        by_contra! hC;
        simpa [Frame.box] using @hC.refl ∅;

end LO.Modal

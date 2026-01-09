module
import Foundation.Modal.Neighborhood.AxiomGeach
import Foundation.Modal.Neighborhood.AxiomM
import Foundation.Modal.Neighborhood.AxiomC
import Foundation.Modal.Neighborhood.Logic.E
import Foundation.Modal.Neighborhood.Logic.ED
import Foundation.Modal.Neighborhood.Filtration
import Foundation.Modal.Entailment.ET

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood


namespace Neighborhood

instance : Frame.simple_blackhole.IsReflexive := by
  constructor;
  intro X x;
  simp_all;

@[reducible] protected alias Frame.IsET := Frame.IsReflexive
protected class Frame.IsFiniteET (F : Frame) extends F.IsET, F.IsFinite

protected abbrev FrameClass.ET : FrameClass := { F | F.IsET }
protected abbrev FrameClass.finite_ET : FrameClass := { F | F.IsFiniteET }

instance {F : Frame} [F.IsReflexive] : F.IsSerial where
  serial := by
    intro X x hx;
    apply F.refl_dual;
    exact F.refl hx;

end Neighborhood


namespace ET

instance Neighborhood.sound : Sound Modal.ET FrameClass.ET := instSound_of_validates_axioms $ by
  simp only [Semantics.ModelsSet.singleton_iff];
  intro F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply valid_axiomT_of_isReflexive;

instance consistent : Entailment.Consistent Modal.ET := consistent_of_sound_frameclass FrameClass.ET $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  infer_instance;

instance Neighborhood.complete : Complete Modal.ET FrameClass.ET := (basicCanonicity Modal.ET).completeness $ by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end ET


instance : Modal.ED ⪱ Modal.ET := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_provable_axioms;
    rintro φ rfl; simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.T (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.ED);
      apply not_validOnFrameClass_of_exists_frame;
      use ⟨Fin 1, λ _ => {∅}⟩;
      constructor;
      . apply Set.mem_setOf_eq.mpr;
        constructor;
        . intro X x;
          simp_all;
      . apply not_imp_not.mpr isReflexive_of_valid_axiomT;
        by_contra! hC;
        simpa [Frame.box] using @hC.refl ∅;

end LO.Modal

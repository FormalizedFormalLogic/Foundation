import Foundation.Modal.Neighborhood.AxiomGeach
import Foundation.Modal.Neighborhood.AxiomM
import Foundation.Modal.Neighborhood.AxiomC
import Foundation.Modal.Neighborhood.Logic.E
import Foundation.Modal.Neighborhood.Logic.ED
import Foundation.Modal.Neighborhood.Filtration

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

instance : Sound Modal.ET FrameClass.ET := instSound_of_validates_axioms $ by
  simp only [Semantics.RealizeSet.singleton_iff];
  intro F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply valid_axiomT_of_isReflexive;

instance : Entailment.Consistent Modal.ET := consistent_of_sound_frameclass FrameClass.ET $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  infer_instance;

instance : Complete Modal.ET FrameClass.ET := (minimalCanonicity Modal.ET).completeness $ by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

lemma provable_axiomD : Modal.ET ⊢ Axioms.D φ := by
  suffices Modal.ET ⊢ Axioms.D (.atom 0) by apply Logic.subst (s := λ n => φ) this;
  apply Complete.complete (𝓜 := FrameClass.ET);
  intro F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply valid_axiomD_of_isSerial;

noncomputable instance : Entailment.HasAxiomD Modal.ET := ⟨λ _ => provable_axiomD.some⟩

end ET


instance : Modal.ED ⪱ Modal.ET := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_provable_axioms;
    rintro φ (rfl);
    . simp;
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

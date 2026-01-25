module

public import Foundation.Modal.Neighborhood.AxiomC
public import Foundation.Modal.Neighborhood.AxiomGeach
public import Foundation.Modal.Neighborhood.AxiomP
public import Foundation.Modal.Neighborhood.AxiomN
public import Foundation.Modal.Neighborhood.Logic.E

@[expose] public section

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

instance : Frame.simple_blackhole.NotContainsEmpty := by
  constructor;
  simp only [Set.mem_singleton_iff, forall_const];
  tauto_set;


@[reducible] protected alias Frame.IsEP := Frame.NotContainsEmpty
protected abbrev FrameClass.EP : FrameClass := { F | F.IsEP }


end Neighborhood


namespace EP

instance Neighborhood.sound : Sound Modal.EP FrameClass.EP := instSound_of_validates_axioms $ by
  simp only [Semantics.ModelsSet.singleton_iff];
  intro F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  simp;

instance consistent : Entailment.Consistent Modal.EP := consistent_of_sound_frameclass FrameClass.EP $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  infer_instance;

@[simp]
lemma unprovable_AxiomD : Modal.EP ⊬ Axioms.D (.atom a) := by
  apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EP);
  apply not_validOnFrameClass_of_exists_frame;
  use ⟨Fin 2, λ w => match w with | 0 => {{0}} | 1 => {{0},{1},{0,1}}⟩
  constructor;
  . constructor;
    intro x;
    match x with | 0 => simp; | 1 => simp; tauto_set;
  . apply not_imp_not.mpr isSerial_of_valid_axiomD;
    by_contra! hC;
    have := @hC |>.serial {1} 1;
    simp [Frame.box, Frame.dia] at this;
    tauto_set;

end EP

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
end

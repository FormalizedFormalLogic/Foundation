module

public import Foundation.Modal.Neighborhood.AxiomGeach
public import Foundation.Modal.Neighborhood.AxiomM
public import Foundation.Modal.Neighborhood.AxiomC
public import Foundation.Modal.Neighborhood.Logic.E
public import Foundation.Modal.Neighborhood.Filtration

@[expose] public section

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood


@[reducible] protected alias Frame.IsE5 := Frame.IsEuclidean
protected class Frame.IsFiniteE5 (F : Frame) extends F.IsE5, F.IsFinite

protected abbrev FrameClass.E5 : FrameClass := { F | F.IsE5 }
protected abbrev FrameClass.finite_E5 : FrameClass := { F | F.IsFiniteE5 }

instance : Frame.simple_blackhole.IsEuclidean := by
  constructor;
  intro X x hx;
  simp_all [(show X ≠ ∅ by grind), Frame.box];

abbrev counterframe_axiomFive : Frame := ⟨Fin 3, λ x => {{x}, Set.univ}⟩

instance : counterframe_axiomFive.IsRegular := by
  constructor;
  rintro X Y x ⟨(rfl | rfl), (rfl | rfl)⟩ <;>
  match x with | 0 | 1 | 2 => simp_all;

@[simp]
lemma counterframe_axiomFive.not_valid_axiomFive : ¬counterframe_axiomFive ⊧ Axioms.Five (Formula.atom 0) := by
  apply not_imp_not.mpr isEuclidean_of_valid_axiomFive;
  by_contra! hC;
  have := hC.eucl {0, 1};
  have := @this 1 $ by
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Set.compl_univ_iff, not_or];
    tauto_set;
  simp only [Frame.box, Frame.dia, Set.mem_insert_iff, Set.mem_singleton_iff, Set.compl_univ_iff, Set.mem_setOf_eq] at this;
  rcases this with (h | h);
  . have := Set.ext_iff.mp h 1 |>.2 (by simp);
    simp at this;
    tauto_set;
  . tauto_set;

end Neighborhood

namespace E5

instance Neighborhood.sound : Sound Modal.E5 FrameClass.E5 := instSound_of_validates_axioms $ by
  simp only [Semantics.ModelsSet.singleton_iff];
  intro F hF;
  replace hF := Set.mem_setOf_eq.mp hF;
  apply valid_axiomFive_of_isEuclidean;

instance consistent : Entailment.Consistent Modal.E5 := consistent_of_sound_frameclass FrameClass.E5 $ by
  use Frame.simple_blackhole;
  apply Set.mem_setOf_eq.mpr;
  infer_instance

instance Neighborhood.complete : Complete Modal.E5 FrameClass.E5 := (maximalRelativeMaximalCanonicity _).completeness $ by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end E5

instance : Modal.E ⪱ Modal.E5 := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.Five (.atom 0));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E);
      apply not_validOnFrameClass_of_exists_frame;
      use counterframe_axiomFive;
      constructor;
      . simp;
      . simp;

end LO.Modal
end

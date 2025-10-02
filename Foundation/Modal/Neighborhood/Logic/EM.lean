import Foundation.Modal.Neighborhood.Logic.E
import Foundation.Modal.Neighborhood.Supplementation
import Foundation.Modal.Neighborhood.AxiomC
import Foundation.Vorspiel.Set.Fin

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

@[reducible] protected alias Frame.IsEM := Frame.IsMonotonic
protected abbrev FrameClass.EM : FrameClass := { F | F.IsEM }

instance : Frame.simple_whitehole.IsEM where
  mono := by simp_all;

abbrev counterframe_axiomC₁ : Frame := {
  World := Fin 2,
  𝒩 := λ w =>
    match w with
    | 0 => {{0}, {1}, {0, 1}}
    | 1 => {{1}, {0, 1}}
}

instance : counterframe_axiomC₁.IsEM where
  mono := by
    rintro X Y w hw;
    constructor;
    . match w with
      | 0 | 1 =>
        rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl;
        case inr.inl =>
          rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl <;>
          . simp [counterframe_axiomC₁] at hw;
            tauto_set;
        all_goals simp_all [counterframe_axiomC₁];
    . match w with
      | 0 | 1 =>
        rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl;
        case inr.inl =>
          rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
          . simp [counterframe_axiomC₁] at hw;
            tauto_set;
        all_goals simp_all [counterframe_axiomC₁];

@[simp]
lemma counterframe_axiomC₁.not_validate_axiomC : ¬counterframe_axiomC₁ ⊧ Axioms.C (.atom 0) (.atom 1) := by
  apply not_imp_not.mpr $ @isRegular_of_valid_axiomC (F := counterframe_axiomC₁);
  by_contra hC;
  have : ({0} : Set counterframe_axiomC₁) ∩ {1} = {0, 1} := by simpa using @hC.regular {0} {1} 0;
  tauto_set;

end Neighborhood


namespace EM

instance : Sound Modal.EM FrameClass.EM := instSound_of_validates_axioms $ by
  constructor;
  rintro _ rfl F hF;
  simp_all;

instance : Entailment.Consistent Modal.EM := consistent_of_sound_frameclass FrameClass.EM $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  infer_instance;

instance : Complete Modal.EM FrameClass.EM := maximalCanonicalFrame.completeness $ by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end EM

instance : Modal.EM ⪱ Modal.EMN := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.N;
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EM);
      apply not_validOnFrameClass_of_exists_frame;
      use Frame.simple_whitehole;
      constructor;
      . apply Set.mem_setOf_eq.mpr; infer_instance;
      . simp;

instance : Modal.EM ⪱ Modal.EMC := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
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

instance : Modal.E ⪱ Modal.EM := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.M (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E);
      apply not_validOnFrameClass_of_exists_model_world;
      let M : Model := {
        World := Fin 3,
        𝒩 := λ w =>
          match w with
          | 0 => {{1}}
          | 1 => {{0}, {0, 1}}
          | 2 => {{0}, {1, 2}},
        Val := λ w =>
          match w with
          | 0 => {0, 1}
          | 1 => {1, 2}
          | _ => Set.univ
      };
      use M, 0;
      constructor;
      . tauto;
      . simp! [M, Semantics.Realize, Satisfies];
        ext x;
        simp;
        omega;

end LO.Modal

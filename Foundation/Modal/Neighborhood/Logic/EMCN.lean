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


namespace Hilbert

namespace EMCN.Neighborhood

instance : Sound Hilbert.EMCN FrameClass.EMCN := instSound_of_validates_axioms $ by
  simp only [Semantics.RealizeSet.insert_iff, Semantics.RealizeSet.singleton_iff];
  refine ⟨?_, ?_, ?_⟩;
  . intro F hF;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply valid_axiomM_of_isMonotonic;
  . intro F hF;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply valid_axiomC_of_isRegular;
  . intro F hF;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply valid_axiomN_of_ContainsUnit;

instance : Entailment.Consistent Hilbert.EMCN := consistent_of_sound_frameclass FrameClass.EMCN $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  constructor;

end EMCN.Neighborhood

instance : Hilbert.EMC ⪱ Hilbert.EMCN := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.N;
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EMC);
      apply not_validOnFrameClass_of_exists_model_world;
      let M : Model := {
        World := Fin 1,
        N := λ w => ∅,
        Val := λ w => Set.univ
      };
      use M, 0;
      constructor;
      . exact {
          mono := by
            rintro X Y w hw;
            simp_all [M];
          regular := by
            rintro X Y w ⟨hwX, hwY⟩;
            simp_all [M]
        }
      . simp! [M, Semantics.Realize, Satisfies];

instance : Hilbert.ECN ⪱ Hilbert.EMCN := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.M (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.ECN);
      apply not_validOnFrameClass_of_exists_model_world;
      let M : Model := {
        World := Fin 2,
        N := λ w =>
          match w with
          | 0 => {∅, {0, 1}}
          | 1 => {∅, {0, 1}},
        Val := λ w =>
          match w with
          | 0 => {0}
          | 1 => {1}
          | _ => Set.univ
      };
      use M, 0;
      constructor;
      . exact {
          contains_unit := by
            intro x;
            match x with | 0 | 1 => simp_all [M, Set.Fin2.eq_univ];
          regular := by
            rintro X Y w ⟨hwX, hwY⟩;
            match w with
            | 0 | 1 =>
              simp_all only [Fin.isValue, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, M];
              rcases hwX with (rfl | rfl) <;>
              rcases hwY with (rfl | rfl) <;>
              simp;
        }
      . simp! [M, Semantics.Realize, Satisfies];
        tauto_set;

instance : Hilbert.EMN ⪱ Hilbert.EMCN := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.C (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EMN);
      apply not_validOnFrameClass_of_exists_model_world;
      let M : Model := {
        World := Fin 2,
        N := λ w =>
          match w with
          | 0 => {{0}, {1}, {0, 1}}
          | 1 => {{0}, {0, 1}},
        Val := λ w =>
          match w with
          | 0 => {0}
          | 1 => {1}
          | _ => Set.univ
      };
      use M, 0;
      constructor;
      . exact {
          mono := by
            rintro X Y e he;
            constructor;
            . match e with
              | 0 => rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;> simp_all [M];
              | 1 =>
                rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl;
                case inr.inr.inl =>
                  rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl <;>
                  . simp [M] at he; tauto_set;
                all_goals simp_all [M];
            . match e with
              | 0 => rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl <;> simp_all [M];
              | 1 =>
                rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl;
                case inr.inr.inl =>
                  rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
                  . simp [M] at he; tauto_set;
                all_goals simp_all [M];
          contains_unit := by
            rintro e;
            match e with | 0 | 1 => simp_all [M, Set.Fin2.eq_univ];
        }
      . simp! [M, Semantics.Realize, Satisfies];
        tauto_set;

end Hilbert

instance : 𝐄𝐌𝐂 ⪱ 𝐄𝐌𝐂𝐍 := inferInstance
instance : 𝐄𝐂𝐍 ⪱ 𝐄𝐌𝐂𝐍 := inferInstance
instance : 𝐄𝐌𝐍 ⪱ 𝐄𝐌𝐂𝐍 := inferInstance

end LO.Modal

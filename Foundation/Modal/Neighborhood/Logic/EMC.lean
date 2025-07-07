import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.Logic.EM
import Foundation.Modal.Neighborhood.Logic.EC


namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsEMC (F) extends Frame.IsMonotonic F, Frame.IsRegular F where
protected abbrev FrameClass.EMC : FrameClass := { F | F.IsEMC }

end Neighborhood


namespace Hilbert

namespace EMC.Neighborhood

instance : Sound Hilbert.EMC FrameClass.EMC := instSound_of_validates_axioms $ by
  simp only [Semantics.RealizeSet.insert_iff, Semantics.RealizeSet.singleton_iff];
  refine ⟨?_, ?_⟩;
  . intro F hF;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply valid_axiomM_of_isMonotonic;
  . intro F hF;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply valid_axiomC_of_isRegular;

instance : Entailment.Consistent Hilbert.EMC := consistent_of_sound_frameclass FrameClass.EMC $ by
  use Frame.simple_blackhole;
  simp;
  constructor;

end EMC.Neighborhood

instance : Hilbert.EC ⪱ Hilbert.EMC := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.M (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EC);
      apply not_validOnFrameClass_of_exists_model_world;
      let M : Model := {
        World := Fin 3,
        ν := λ w =>
          match w with
          | 0 => {{1}}
          | 1 => {{0}, {0, 1}}
          | 2 => {{0}, {1, 2}, ∅},
        Val := λ w =>
          match w with
          | 0 => {0, 1}
          | 1 => {1, 2}
          | _ => Set.univ
      };
      use M, 0;
      constructor;
      . exact {
          regular := by
            rintro X Y w ⟨hwX, hwY⟩;
            match w with
            | 0 => simp_all [M];
            | 1 =>
              rcases hwX with (rfl | rfl) <;>
              rcases hwY with (rfl | rfl) <;>
              simp_all [M];
            | 2 =>
              rcases hwX with (rfl | rfl | rfl) <;>
              rcases hwY with (rfl | rfl | rfl) <;>
              simp [M]
        }
      . simp! [M, Semantics.Realize, Satisfies];
        ext x;
        simp!;
        omega;

instance : Hilbert.EM ⪱ Hilbert.EMC := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.C (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EM);
      apply not_validOnFrameClass_of_exists_model_world;
      let M : Model := {
        World := Fin 2,
        ν := λ w =>
          match w with
          | 0 => {{0}, {1}, {0, 1}}
          | 1 => {{1}, {0, 1}},
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
            rintro X Y w hw;
            constructor;
            . match w with
              | 0 | 1 =>
                rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl;
                case inr.inl =>
                  rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl <;>
                  . simp [M] at hw; tauto_set;
                all_goals simp_all [M];
            . match w with
              | 0 | 1 =>
                rcases Set.Fin2.all_cases Y with rfl | rfl | rfl | rfl;
                case inr.inl =>
                  rcases Set.Fin2.all_cases X with rfl | rfl | rfl | rfl <;>
                  . simp [M] at hw; tauto_set;
                all_goals simp_all [M];
        }
      . simp! [M, Semantics.Realize, Satisfies];
        tauto_set;

end Hilbert

instance : 𝐄𝐂 ⪱ 𝐄𝐌𝐂 := inferInstance
instance : 𝐄𝐌 ⪱ 𝐄𝐌𝐂 := inferInstance

end LO.Modal

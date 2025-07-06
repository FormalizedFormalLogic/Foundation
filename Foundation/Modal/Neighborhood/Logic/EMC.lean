import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.Logic.EM
import Foundation.Modal.Neighborhood.Logic.EC


lemma _root_.Set.powerset_Fin2 : Set.powerset (Set.univ : Set (Fin 2)) = {{0, 1}, {0}, {1}, ∅} := by
  ext x;
  simp only [Set.powerset_univ, Set.mem_univ, Fin.isValue, Set.mem_insert_iff, Set.mem_singleton_iff, true_iff];
  by_cases h0 : 0 ∈ x <;>
  by_cases h1 : 1 ∈ x;
  . left;
    ext i;
    match i with | 0 | 1 => simp_all;
  . right; left;
    ext i;
    match i with | 0 | 1 => simp_all;
  . right; right; left;
    ext i;
    match i with | 0 | 1 => simp_all;
  . right; right; right;
    ext i;
    match i with | 0 | 1 => simp_all;

lemma _root_.Set.all_cases_Fin2 (s : Set (Fin 2)) : s = {0, 1} ∨ s = {0} ∨ s = {1} ∨ s = ∅ := by
  simpa using Set.powerset_Fin2.subset (by simp);


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
  use Frame.trivial;
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
        simp;
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
            rintro X Y hXY w hwX;
            match w with
            | 0 | 1 =>
              rcases hwX with rfl | rfl | rfl <;>
              rcases Set.all_cases_Fin2 Y with rfl | rfl | rfl | rfl <;>
              tauto_set;
        }
      . simp! [M, Semantics.Realize, Satisfies];
        by_contra! h;
        have := h.symm.subset';
        simp at this;

end Hilbert

instance : 𝐄𝐂 ⪱ 𝐄𝐌𝐂 := inferInstance
instance : 𝐄𝐌 ⪱ 𝐄𝐌𝐂 := inferInstance

end LO.Modal

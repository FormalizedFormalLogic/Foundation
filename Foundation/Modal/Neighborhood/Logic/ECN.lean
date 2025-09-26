import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.Logic.EN
import Foundation.Modal.Neighborhood.Logic.EC

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsECN (F : Frame) extends F.IsRegular, F.ContainsUnit where
protected abbrev FrameClass.ECN : FrameClass := { F | F.IsECN }

end Neighborhood

instance : Sound Modal.ECN FrameClass.ECN := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl) F (rfl | rfl) <;> simp;

instance : Entailment.Consistent Modal.ECN := consistent_of_sound_frameclass FrameClass.ECN $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  constructor;

instance : Complete Modal.ECN FrameClass.ECN := minimalCanonicalFrame.completeness $ by
  apply Set.mem_setOf_eq.mpr;
  constructor;

instance : Modal.EC ⪱ Modal.ECN := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.N;
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EC);
      apply not_validOnFrameClass_of_exists_model_world;
      let M : Model := {
        World := Fin 3,
        𝒩 := λ w =>
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
        tauto_set;

instance : Modal.EN ⪱ Modal.ECN := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.C (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EN);
      apply not_validOnFrameClass_of_exists_model_world;
      let M : Model := {
        World := Fin 2,
        𝒩 := λ w =>
          match w with
          | 0 => {{0}, {1}, {0, 1}, Set.univ}
          | 1 => {{1}, {0, 1}, Set.univ},
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
            ext x;
            match x with | 0 | 1 => simp_all [M]
        }
      . simp! [M, Semantics.Realize, Satisfies];
        tauto_set;



end LO.Modal

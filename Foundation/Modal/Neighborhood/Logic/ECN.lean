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


namespace Hilbert

namespace ECN.Neighborhood

instance : Sound Hilbert.ECN FrameClass.ECN := instSound_of_validates_axioms $ by
  simp only [Semantics.RealizeSet.insert_iff, Semantics.RealizeSet.singleton_iff];
  refine ⟨?_, ?_⟩;
  . intro F hF;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply valid_axiomC_of_isRegular;
  . intro F hF;
    replace hF := Set.mem_setOf_eq.mp hF;
    apply valid_axiomN_of_ContainsUnit;

instance : Entailment.Consistent Hilbert.ECN := consistent_of_sound_frameclass FrameClass.ECN $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  constructor;

end ECN.Neighborhood

instance : Hilbert.EC ⪱ Hilbert.ECN := by
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
        N := λ w =>
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

instance : Hilbert.EN ⪱ Hilbert.ECN := by
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
        N := λ w =>
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
            intro x;
            match x with | 0 | 1 => simp_all [M]
        }
      . simp! [M, Semantics.Realize, Satisfies];
        tauto_set;

end Hilbert

instance : 𝐄𝐂 ⪱ 𝐄𝐂𝐍 := inferInstance
instance : 𝐄𝐍 ⪱ 𝐄𝐂𝐍 := inferInstance

end LO.Modal

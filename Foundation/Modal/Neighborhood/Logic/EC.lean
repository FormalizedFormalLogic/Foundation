import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.AxiomC
import Foundation.Modal.Neighborhood.Logic.E
import Foundation.Modal.Neighborhood.Supplementation

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

@[reducible] protected alias Frame.IsEC := Frame.IsRegular
protected abbrev FrameClass.EC : FrameClass := { F | F.IsEC }

end Neighborhood

namespace EC

instance Neighborhood.sound : Sound Modal.EC FrameClass.EC := instSound_of_validates_axioms $ by
  constructor;
  rintro _ rfl F hF;
  simp_all;

instance consistent : Entailment.Consistent Modal.EC := consistent_of_sound_frameclass FrameClass.EC $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  infer_instance;

instance Neighborhood.complete : Complete Modal.EC FrameClass.EC := (minimalCanonicity Modal.EC).completeness $ by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end EC


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

instance : Modal.EC ⪱ Modal.EMC := by
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
        ext x;
        simp!;
        omega;

end LO.Modal

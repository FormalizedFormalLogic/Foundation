module
import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.Logic.EN
import Foundation.Modal.Neighborhood.Logic.EC
import Foundation.Vorspiel.Set.Fin

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsECN (F : Frame) extends F.IsRegular, F.ContainsUnit where
protected abbrev FrameClass.ECN : FrameClass := { F | F.IsECN }

end Neighborhood


namespace ECN

instance Neighborhood.sound : Sound Modal.ECN FrameClass.ECN := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl) F (rfl | rfl) <;> simp;

instance consistent : Entailment.Consistent Modal.ECN := consistent_of_sound_frameclass FrameClass.ECN $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  constructor;

instance Neighborhood.complete : Complete Modal.ECN FrameClass.ECN := (basicCanonicity Modal.ECN).completeness $ by
  apply Set.mem_setOf_eq.mpr;
  constructor;

end ECN


instance : Modal.ECN ⪱ Modal.EMCN := by
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
        𝒩 := λ w => {∅, {0, 1}},
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
            match x with | 0 | 1 => simp_all [M, Set.Fin2.eq_univ];
          regular := by
            rintro X Y w ⟨hwX, hwY⟩;
            simp_all only [Fin.isValue, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, M];
            rcases hwX with (rfl | rfl) <;>
            rcases hwY with (rfl | rfl) <;>
            simp;
        }
      . simp [M, Semantics.Models, Satisfies];
        grind;

end LO.Modal

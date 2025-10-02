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

instance : Sound Modal.EMCN FrameClass.EMCN := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl | rfl) F (rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent Modal.EMCN := consistent_of_sound_frameclass FrameClass.EMCN $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  constructor;

instance : Complete Modal.EMCN FrameClass.EMCN := maximalCanonicalFrame.completeness $ by
  apply Set.mem_setOf_eq.mpr;
  constructor;

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
      . simp! [M, Semantics.Realize, Satisfies];
        tauto_set;


end LO.Modal

module

public import Foundation.Modal.Neighborhood.Hilbert
public import Foundation.Modal.Neighborhood.AxiomN
public import Foundation.Modal.Neighborhood.Logic.E
public import Foundation.Modal.PLoN.Logic.N

@[expose] public section

namespace LO.Modal

open Formula (atom)
open Entailment
open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

@[reducible] protected alias Frame.IsEN := Frame.ContainsUnit
protected abbrev FrameClass.EN : FrameClass := { F | F.IsEN }

end Neighborhood


namespace EN

instance Neighborhood.sound : Sound Modal.EN FrameClass.EN := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl) F hF;
  simp_all;

instance consistent : Entailment.Consistent Modal.EN := consistent_of_sound_frameclass FrameClass.EN $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  infer_instance;

instance Neighborhood.complete : Complete Modal.EN FrameClass.EN := (basicCanonicity Modal.EN).completeness $ by
  apply Set.mem_setOf_eq.mpr;
  infer_instance;

end EN


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
      . simp! [M, Semantics.Models, Satisfies];
        tauto_set;

instance : Modal.EN ⪱ Modal.EMN := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.M (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EN);
      apply not_validOnFrameClass_of_exists_model_world;
      let M : Model := {
        World := Fin 2,
        𝒩 := λ w =>
          match w with
          | 0 => {∅, Set.univ}
          | 1 => {Set.univ},
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
      . simp! [M, Semantics.Models, Satisfies];


end LO.Modal
end

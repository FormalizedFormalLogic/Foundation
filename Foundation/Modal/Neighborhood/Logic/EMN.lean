import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.Logic.EN
import Foundation.Modal.Neighborhood.Logic.EM



namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsEMN (F : Frame) extends F.IsMonotonic, F.ContainsUnit where
protected abbrev FrameClass.EMN : FrameClass := { F | F.IsEMN }

end Neighborhood


namespace Hilbert

namespace EMN.Neighborhood

instance : Sound Hilbert.EMN FrameClass.EMN := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl) F (rfl | rfl | rfl) <;> simp;

instance : Entailment.Consistent Hilbert.EMN := consistent_of_sound_frameclass FrameClass.EMN $ by
  use Frame.simple_blackhole;
  simp only [Set.mem_setOf_eq];
  constructor;

instance : Complete Hilbert.EMN FrameClass.EMN := complete_of_canonical_frame FrameClass.EMN (maximalCanonicalFrame (Hilbert.EMN)) $ by
  apply Set.mem_setOf_eq.mpr;
  constructor;

end EMN.Neighborhood

instance : Hilbert.EM ⪱ Hilbert.EMN := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.N;
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EM);
      apply not_validOnFrameClass_of_exists_model_world;
      let M : Model := {
        World := Fin 1,
        𝒩 := λ w => ∅,
        Val := λ w => Set.univ
      };
      use M, 0;
      constructor;
      . exact { mono := by rintro X Y w hw; simp_all [M] }
      . simp! [M, Semantics.Realize, Satisfies];

instance : Hilbert.EN ⪱ Hilbert.EMN := by
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
      . simp! [M, Semantics.Realize, Satisfies];

end Hilbert

instance : 𝐄𝐌 ⪱ 𝐄𝐌𝐍 := inferInstance
instance : 𝐄𝐍 ⪱ 𝐄𝐌𝐍 := inferInstance

end LO.Modal

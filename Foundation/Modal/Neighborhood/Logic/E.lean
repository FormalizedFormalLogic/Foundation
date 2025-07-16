import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.Completeness

namespace LO.Modal

open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

abbrev FrameClass.E : FrameClass := Set.univ

end Neighborhood


namespace Hilbert.E.Neighborhood

instance : Sound Hilbert.E FrameClass.E := instSound_of_validates_axioms $ by simp;

instance : Entailment.Consistent Hilbert.E := consistent_of_sound_frameclass FrameClass.E $ by
  use ⟨Unit, λ _ => {}⟩;
  simp;

instance : Complete Hilbert.E FrameClass.E := complete_of_canonical_frame FrameClass.E (minimal_canonical_box (Hilbert.E)) (by tauto)

instance : Hilbert.E ⪱ Hilbert.EK := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.K (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E);
      apply not_validOnFrameClass_of_exists_model_world;
      let M : Model := {
        World := Fin 3,
        𝒩 := λ w =>
          match w with
          | 0 => {{0}, {0, 1, 2}}
          | 1 => ∅
          | 2 => ∅,
        Val := λ w =>
          match w with
          | 0 => {0}
          | 1 => {0, 1}
          | _ => Set.univ
      };
      use M, 0;
      constructor;
      . tauto;
      . simp! [M, Semantics.Realize, Satisfies];
        constructor;
        . intro;
          ext x;
          simp;
          omega;
        . tauto_set;

instance : Hilbert.E ⪱ Hilbert.EN := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_subset_axioms;
    simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.N
    constructor;
    . simp;
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.E);
      apply not_validOnFrameClass_of_exists_model_world;
      let M : Model := {
        World := Fin 1,
        𝒩 := λ w => ∅,
        Val := λ w => Set.univ
      };
      use M, 0;
      constructor;
      . tauto;
      . simp! [M, Semantics.Realize, Satisfies];

end Hilbert.E.Neighborhood

instance : 𝐄 ⪱ 𝐄𝐍 := inferInstance
instance : 𝐄 ⪱ 𝐄𝐊 := inferInstance

end LO.Modal

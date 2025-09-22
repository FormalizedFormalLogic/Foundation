import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.Logic.EM
import Foundation.Modal.Neighborhood.Logic.EC
import Foundation.Vorspiel.Set.Fin


namespace LO.Modal

open Formula (atom)
open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Neighborhood

protected class Frame.IsEMC (F) extends Frame.IsMonotonic F, Frame.IsRegular F where
protected abbrev FrameClass.EMC : FrameClass := { F | F.IsEMC }

abbrev EK_counterframe_for_M_and_C : Frame := {
  World := Fin 4,
  𝒩 := λ _ => {{0, 1}, {0, 2}}
}

lemma EK_counterframe_for_M_and_C.validate_axiomK : EK_counterframe_for_M_and_C ⊧ Axioms.K (atom 0) (atom 1) := by
  intro V x;
  apply Satisfies.def_imp.mpr;
  intro h₁; replace h₁ := Satisfies.def_box.mp h₁;
  apply Satisfies.def_imp.mpr;
  intro h₂; replace h₂ := Satisfies.def_box.mp h₂;
  apply Satisfies.def_box.mpr;
  simp_all only [Fin.isValue, Model.truthset.eq_imp, Model.truthset.eq_atom, Set.mem_insert_iff, Set.mem_singleton_iff];
  rcases h₂ with h₂ | h₂ <;> rcases h₁ with h₁ | h₁ <;>
  . have := h₁.subset;
    have := @this 3 $ by simp [h₂];
    simp at this;

lemma EK_counterframe_for_M_and_C.validate_axiomC : ¬EK_counterframe_for_M_and_C ⊧ Axioms.C (atom 0) (atom 1) := by
  apply ValidOnFrame.not_of_exists_valuation_world;
  use (λ a =>
    match a with
    | 0 => {0, 1}
    | 1 => {0, 2}
    | _ => ∅
  ), 0;
  simp [Satisfies];

lemma EK_counterframe_for_M_and_C.validate_axiomM : ¬EK_counterframe_for_M_and_C ⊧ Axioms.M ((atom 0) ⋎ (atom 1)) (atom 1) := by
  apply ValidOnFrame.not_of_exists_valuation_world;
  use (λ a =>
    match a with
    | 0 => {0, 1}
    | 1 => {0, 2}
    | _ => ∅
  ), 0;
  suffices (({0, 2} : Set (Fin 4)) ⊆ {2, 0, 1}) ∧ ({2, 0, 1} : Set (Fin 4)) ≠ {0, 2} by
    simp [Satisfies];
    grind;
  constructor;
  . intro x;
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff];
    tauto;
  . by_contra hC;
    have := hC.subset;
    simpa using @this 1 (by simp)

end Neighborhood


instance : Sound Modal.EMC FrameClass.EMC := instSound_of_validates_axioms $ by
  constructor;
  rintro _ (rfl | rfl) F (rfl | rfl) <;> simp;

instance : Entailment.Consistent Modal.EMC := consistent_of_sound_frameclass FrameClass.EMC $ by
  use Frame.simple_blackhole;
  simp;
  constructor;

instance : Complete Modal.EMC FrameClass.EMC := complete_of_canonical_frame FrameClass.EMC (maximalCanonicalFrame (Modal.EMC)) $ by
  apply Set.mem_setOf_eq.mpr;
  constructor;

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

instance : Modal.EM ⪱ Modal.EMC := by
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
        𝒩 := λ w =>
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
          -- TODO: need golf!
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

instance : Modal.EK ⪱ Modal.EMC := by
  constructor;
  . apply Hilbert.WithRE.weakerThan_of_provable_axioms;
    rintro φ rfl; simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use (Axioms.C (.atom 0) (.atom 1));
    constructor;
    . simp;
    . apply not_imp_not.mpr $ soundness_of_axioms_validOnFrame (F := EK_counterframe_for_M_and_C) ?_;
      . apply EK_counterframe_for_M_and_C.validate_axiomC;
      . simp only [Semantics.RealizeSet.singleton_iff];
        apply EK_counterframe_for_M_and_C.validate_axiomK;

end LO.Modal

import Foundation.Modal.Neighborhood.AxiomGeach
import Foundation.Modal.Neighborhood.AxiomK
import Foundation.Modal.Neighborhood.Hilbert
import Foundation.Modal.Neighborhood.Logic.E4
import Foundation.Modal.Neighborhood.Logic.EC
import Foundation.Modal.Neighborhood.Logic.EM
import Foundation.Vorspiel.Set.Fin


namespace LO.Modal

open Formula (atom)
open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood


namespace Neighborhood

variable {a b}

abbrev EK_counterframe_for_M_and_C : Frame := {
  World := Fin 4,
  𝒩 := λ _ => {{0, 1}, {0, 2}}
}

instance : EK_counterframe_for_M_and_C.HasPropertyK where
  K := by
    intro X Y w;
    suffices Xᶜ ∪ Y = {0, 1} ∨ Xᶜ ∪ Y = {0, 2} → X = {0, 1} ∨ X = {0, 2} → Y = {0, 1} ∨ Y = {0, 2} by simpa;
    rintro (h₁ | h₁) (h₂ | h₂) <;>
    . have := h₁.subset;
      have := @this 3 (by simp [h₂]);
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
    tauto_set;
  constructor;
  . intro x;
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff];
    tauto;
  . by_contra hC;
    have := hC.subset;
    simpa using @this 1 (by simp)

end Neighborhood


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
      . simp;

end LO.Modal

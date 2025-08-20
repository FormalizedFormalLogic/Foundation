import Foundation.Modal.Neighborhood.Logic.EP
import Foundation.Modal.Neighborhood.Logic.ED

namespace LO.Modal

open LO.Entailment (Incomparable)
open Neighborhood
open Hilbert.Neighborhood
open Formula.Neighborhood

namespace Hilbert

@[simp]
lemma EP.unprovable_AxiomD : Hilbert.EP ⊬ Axioms.D (.atom a) := by
  apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.EP)
  apply not_validOnFrameClass_of_exists_frame
  use ⟨Fin 2, λ w => match w with | 0 => {{0}} | 1 => {{0},{1},{0,1}}⟩
  constructor
  . constructor
    intro x
    match x with
    | 0 | 1 => simp; tauto_set
  . apply not_imp_not.mpr isSerial_of_valid_axiomD
    by_contra! hC
    have := @hC |>.serial {1} 1
    simp [Frame.box, Frame.dia] at this
    tauto_set

instance : Incomparable Hilbert.ED Hilbert.EP := by
  apply Incomparable.of_unprovable
  . use (Axioms.D (.atom 0))
    constructor
    . simp
    . exact EP.unprovable_AxiomD
  . use (Axioms.P)
    constructor
    . simp
    . apply Sound.not_provable_of_countermodel (𝓜 := FrameClass.ED)
      apply not_validOnFrameClass_of_exists_frame
      use ⟨Fin 2, λ x => match x with | 0 => {∅, {1}} | 1 => {∅, {0}}⟩
      constructor
      . constructor
        intro X x
        match x with
        | 0 | 1 =>
          rintro (rfl | rfl)
          . simp; tauto_set
          . simp
      . apply not_imp_not.mpr notContainsEmpty_of_valid_axiomP
        by_contra! hC
        have := hC |>.not_contains_empty
        simpa using @this 1

end Hilbert

instance : Entailment.Incomparable 𝐄𝐃 𝐄𝐏 := inferInstance

end LO.Modal

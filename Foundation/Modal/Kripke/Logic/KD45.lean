import Foundation.Modal.Kripke.AxiomGeach
import Foundation.Modal.Kripke.Hilbert
import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.Kripke.Logic.KD4
import Foundation.Modal.Kripke.Logic.KD5
import Foundation.Modal.Kripke.Logic.K45

namespace LO.Modal

open Kripke
open Hilbert.Kripke
open GeachConfluent

abbrev Kripke.FrameClass.serial_trans_eucl : FrameClass := { F | IsSerial _ F ∧ IsTrans _ F ∧ IsEuclidean _ F }

namespace Hilbert.KD45.Kripke

instance sound : Sound (Hilbert.KD45) Kripke.FrameClass.serial_trans_eucl := instSound_of_validates_axioms $ by
  apply FrameClass.Validates.withAxiomK;
  rintro F ⟨_, _, _⟩ _ (rfl | rfl | rfl);
  . exact validate_AxiomD_of_serial;
  . exact validate_AxiomFour_of_transitive;
  . exact validate_AxiomFive_of_euclidean;

instance consistent : Entailment.Consistent (Hilbert.KD45) := consistent_of_sound_frameclass Kripke.FrameClass.serial_trans_eucl $ by
  use whitepoint;
  refine ⟨inferInstance, inferInstance, inferInstance⟩;

instance canonical : Canonical (Hilbert.KD45) Kripke.FrameClass.serial_trans_eucl := ⟨by
  apply Set.mem_setOf_eq.mpr;
  refine ⟨inferInstance, inferInstance, inferInstance⟩;
⟩

instance complete : Complete (Hilbert.KD45) Kripke.FrameClass.serial_trans_eucl := inferInstance

end Hilbert.KD45.Kripke

namespace Logic

open Formula
open Entailment
open Kripke

lemma KD45.Kripke.serial_trans_eucl : Logic.KD45 = FrameClass.serial_trans_eucl.logic := eq_hilbert_logic_frameClass_logic

theorem KD45.proper_extension_of_K5 : Logic.KD4 ⊂ Logic.KD45 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KD45 ⊢! φ ∧ ¬FrameClass.serial_trans ⊧ φ by
      rw [KD4.Kripke.serial_trans];
      tauto;
    use Axioms.Five (.atom 0);
    constructor;
    . exact axiomFive!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨
          ⟨Fin 3, λ x y => x = y ∨ x < y⟩,
          λ w _ => w = 0
        ⟩;
      use M, 0;
      constructor;
      . refine ⟨⟨by tauto⟩, ⟨by omega⟩⟩;
      . suffices (0 : M.World) ≺ 0 ∧ ∃ x : M.World, (0 : M.World) ≺ x ∧ ¬x ≺ 0 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . tauto;
        . use 1;
          constructor <;> omega;

theorem KD45.proper_extension_of_KD5 : Logic.KD5 ⊂ Logic.KD45 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KD45 ⊢! φ ∧ ¬FrameClass.serial_eucl ⊧ φ by
      rw [KD5.Kripke.serial_eucl];
      tauto;
    use (Axioms.Four (.atom 0));
    constructor;
    . exact axiomFour!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 3, λ x y => (x = 0 ∧ y = 1) ∨ (x ≠ 0 ∧ y ≠ 0)⟩, λ w _ => w = 1⟩;
      use M, 0;
      constructor;
      . refine ⟨⟨?_⟩, ⟨by unfold Euclidean; omega⟩⟩;
        . intro x;
          match x with
          | 0 => use 1; tauto;
          | 1 => use 1; omega;
          | 2 => use 2; omega;
      . suffices (∀ (y : M.World), (0 : M.World) ≺ y → y = 1) ∧ ∃ x, (0 : M.World) ≺ x ∧ ∃ y, x ≺ y ∧ y ≠ 1 by
          simpa [M, Semantics.Realize, Satisfies];
        constructor;
        . intro y;
          match y with
          | 0 => tauto;
          | 1 => tauto;
          | 2 => tauto;
        . use 1;
          constructor;
          . tauto;
          . use 2;
            constructor;
            . omega;
            . trivial;

theorem KD45.proper_extension_of_K45 : Logic.K45 ⊂ Logic.KD45 := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KD45 ⊢! φ ∧ ¬FrameClass.trans_eucl ⊧ φ by
      rw [K45.Kripke.trans_eucl];
      tauto;
    use Axioms.D (.atom 0);
    constructor;
    . exact axiomD!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => False⟩, λ w _ => True⟩, 0;
      constructor;
      . refine ⟨⟨by tauto⟩, ⟨by tauto⟩⟩;
      . simp [Semantics.Realize, Satisfies];

end Logic


end LO.Modal

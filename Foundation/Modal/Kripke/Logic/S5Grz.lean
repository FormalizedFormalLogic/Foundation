import Foundation.Modal.Hilbert.S5Grz
import Foundation.Modal.Kripke.Logic.Grz.Completeness
import Foundation.Modal.Kripke.Logic.Triv
import Foundation.Modal.Kripke.Logic.S5

namespace LO.Modal.Logic

open Entailment
open Formula
open Kripke
open Hilbert.Kripke

lemma S5Grz.Kripke.finite_equality : Logic.S5Grz = Kripke.FrameClass.finite_Triv.logic := by simp [Triv.Kripke.finite_equality]

instance : Logic.S5 ⪱ Logic.S5Grz := by
  constructor;
  . exact Hilbert.weakerThan_of_subset_axioms (by simp)
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Grz (.atom 0);
    constructor;
    . simp;
    . suffices ¬FrameClass.universal ⊧ (Axioms.Grz (.atom 0)) by simpa [S5.Kripke.universal];
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 1⟩, 0;
      constructor;
      . exact { universal := by tauto; };
      . simp [Semantics.Realize, Satisfies];
        tauto;

instance : Logic.S5 ⪱ Logic.Triv := by
  suffices Logic.S5 ⪱ Logic.S5Grz by simpa;
  infer_instance

instance : Logic.Grz ⪱ Logic.S5Grz := by
  constructor;
  . apply Hilbert.weakerThan_of_provable_axioms;
    rintro _ (rfl | rfl | rfl) <;> simp;
  . apply Entailment.not_weakerThan_iff.mpr;
    use Axioms.Five (.atom 0)
    constructor;
    . simp;
    . suffices ¬FrameClass.finite_Grz ⊧ Axioms.Five (.atom 0) by simpa [Grz.Kripke.finite_partial_order];
      apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≤ y⟩, (λ w _ => w = 0)⟩;
      use M, 0;
      constructor;
      . refine {
          refl := by omega,
          trans := by omega;
          antisymm := by simp [M]; omega;
        };
      . suffices (0 : M.World) ≺ 0 ∧ ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 0 by
          simpa [Semantics.Realize, Satisfies, ValidOnFrame, M];
        constructor;
        . omega;
        . use 1;
          constructor <;> omega;

instance : Logic.S4 ⪱ Logic.Triv := calc
  Logic.S4 ⪱ Logic.S5   := by infer_instance
  _        ⪱ Logic.Triv := by infer_instance

end LO.Modal.Logic

import Foundation.Modal.Hilbert.S5Grz
import Foundation.Modal.Kripke.Logic.Grz.Completeness
import Foundation.Modal.Kripke.Logic.Triv
import Foundation.Modal.Kripke.Logic.S5

namespace LO.Modal.Logic

open Formula
open Entailment
open Kripke

lemma S5Grz.Kripke.finite_equality : Logic.S5Grz = Kripke.FrameClass.finite_equality.logic := by
  rw [eq_S5Grz_Triv, Triv.Kripke.finite_equality]

instance : ProperSublogic Logic.S5 Logic.S5Grz := ⟨by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.S5Grz ⊢! φ ∧ ¬FrameClass.universal ⊧ φ by
      rw [S5.Kripke.universal];
      tauto;
    use Axioms.Grz (.atom 0);
    constructor;
    . exact axiomGrz!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 1⟩, 0;
      constructor;
      . refine ⟨by simp [Universal]⟩;
      . simp [Semantics.Realize, Satisfies];
⟩

instance : ProperSublogic Logic.Grz Logic.S5Grz := ⟨by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.S5Grz ⊢! φ ∧ ¬FrameClass.finite_partial_order ⊧ φ by
      rw [Grz.Kripke.finite_partial_order];
      tauto;
    use Axioms.Five (.atom 0)
    constructor;
    . exact axiomFive!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      let M : Model := ⟨⟨Fin 2, λ x y => x ≤ y⟩, (λ w _ => w = 0)⟩;
      use M, 0;
      constructor;
      . refine ⟨by tauto, {
          refl := by omega,
          trans := by omega;
          antisymm := by simp [M]; omega;
        }⟩;
      . suffices (0 : M.World) ≺ 0 ∧ ∃ x, (0 : M.World) ≺ x ∧ ¬x ≺ 0 by
          simpa [Semantics.Realize, Satisfies, ValidOnFrame, M];
        constructor;
        . omega;
        . use 1;
          constructor <;> omega;
⟩

instance : ProperSublogic Logic.S5 Logic.Triv := by
  rw [←eq_S5Grz_Triv];
  infer_instance;

instance : ProperSublogic Logic.S4 Logic.Triv := ProperSublogic.trans Logic.S4 Logic.S5 Logic.Triv

end LO.Modal.Logic

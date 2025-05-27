import Foundation.Modal.Logic.Sublogic.ModalCube
import Foundation.Modal.Hilbert.S5Grz
import Foundation.Modal.Kripke.Hilbert.Triv

namespace LO.Modal.Logic

open Formula
open Entailment
open Kripke

lemma S5_ssubset_S5Grz : Logic.S5 ⊂ Logic.S5Grz := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.S5Grz ⊢! φ ∧ ¬FrameClass.universal ⊧ φ by
      rw [S5.Kripke.universal];
      tauto;
    use Axioms.Grz (.atom 0)
    constructor;
    . exact axiomGrz!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 1⟩, 0;
      constructor;
      . refine ⟨by simp [Universal]⟩;
      . simp [Semantics.Realize, Satisfies];
instance : ProperSublogic Logic.S5 Logic.S5Grz := ⟨S5_ssubset_S5Grz⟩


lemma S5Grz_eq_Triv : Logic.S5Grz = Logic.Triv := by
  ext φ;
  exact Hilbert.iff_provable_S5Grz_provable_Triv;


lemma S5Grz.Kripke.eq_finite_equality_logic : Logic.S5Grz = Kripke.FrameClass.finite_equality.logic := by
  rw [S5Grz_eq_Triv, Triv.Kripke.finite_equality]


theorem S5_ssubset_Triv : Logic.S5 ⊂ Logic.Triv := by
  convert S5_ssubset_S5Grz;
  exact S5Grz_eq_Triv.symm;
instance : ProperSublogic Logic.S5 Logic.Triv := ⟨S5_ssubset_Triv⟩

-- TODO: This result should be proved by Makinson's Theorem.
lemma S4_ssubset_Triv : Logic.S4 ⊂ Logic.Triv := by
  trans Logic.S5;
  . exact S4_ssubset_S5;
  . exact S5_ssubset_Triv;

end LO.Modal.Logic

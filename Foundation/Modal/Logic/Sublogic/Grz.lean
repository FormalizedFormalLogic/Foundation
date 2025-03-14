import Foundation.Modal.Logic.Sublogic.S5Grz

namespace LO.Modal.Logic

open Formula
open Entailment
open Kripke

theorem S4_ssubset_Grz : Logic.S4 ⊂ Logic.Grz := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.Grz ⊢! φ ∧ ¬Kripke.FrameClass.preorder ⊧ φ by simpa [S4.eq_ReflexiveTransitiveKripkeFrameClass_Logic];
    use Axioms.Grz (.atom 0)
    constructor;
    . exact axiomGrz!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 1⟩, 0;
      simp [Reflexive, Transitive, Semantics.Realize, Satisfies];
instance : ProperSublogic Logic.S4 Logic.Grz := ⟨S4_ssubset_Grz⟩

lemma Grz_ssubset_S5Grz : Logic.Grz ⊂ Logic.S5Grz := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.S5Grz ⊢! φ ∧ ¬FrameClass.finite_partial_order ⊧ φ by simpa [Grz.eq_ReflexiveTransitiveAntiSymmetricFiniteKripkeFrameClass_Logic];
    use Axioms.Five (.atom 0)
    constructor;
    . exact axiomFive!;
    . apply Kripke.not_validOnFrameClass_of_exists_frame;
      let F : Frame := ⟨Fin 2, λ x y => x ≤ y⟩;
      use F;
      constructor;
      . refine ⟨by tauto, ?_, ?_, ?_⟩;
        . simp [F, Reflexive];
        . simp [F, Transitive]; omega;
        . simp [F, AntiSymmetric]; omega;
      . apply ValidOnFrame.not_of_exists_valuation_world;
        use (λ w _ => w = 0), 0;
        suffices (0 : F.World) ≺ 0 ∧ ∃ x, (0 : F.World) ≺ x ∧ ¬x ≺ 0 by
          simpa [Semantics.Realize, Satisfies, ValidOnFrame];
        constructor;
        . omega;
        . use 1;
          constructor <;> omega;

theorem Grz_ssubset_Triv : Logic.Grz ⊂ Logic.Triv := by
  convert Grz_ssubset_S5Grz;
  exact S5Grz_eq_Triv.symm;
instance : ProperSublogic Logic.Grz Logic.Triv := ⟨Grz_ssubset_Triv⟩

end LO.Modal.Logic

import Foundation.Modal.Logic.WellKnown

namespace LO.Modal.Logic

open Formula
open Entailment
open Kripke

lemma S5_ssubset_S5Grz : Logic.S5 ⊂ Logic.S5Grz := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.S5Grz ⊢! φ ∧ ¬UniversalFrameClass ⊧ φ by simpa [S5.eq_UniversalKripkeFrameClass_Logic];
    use Axioms.Grz (.atom 0)
    constructor;
    . exact axiomGrz!;
    . apply Formula.Kripke.ValidOnFrameClass.not_of_exists_model_world;
      use ⟨⟨Fin 2, λ x y => True⟩, λ w _ => w = 1⟩, 0;
      simp [Universal, Semantics.Realize, Satisfies];
instance : ProperSublogic Logic.S5 Logic.S5Grz := ⟨S5_ssubset_S5Grz⟩

lemma S5Grz_eq_Triv : Logic.S5Grz = Logic.Triv := by
  ext φ;
  exact Hilbert.iff_provable_S5Grz_provable_Triv;

theorem S5_ssubset_Triv : Logic.S5 ⊂ Logic.Triv := by
  convert S5_ssubset_S5Grz;
  exact S5Grz_eq_Triv.symm;
instance : ProperSublogic Logic.S5 Logic.Triv := ⟨S5_ssubset_Triv⟩


end LO.Modal.Logic

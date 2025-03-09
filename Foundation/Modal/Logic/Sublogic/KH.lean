import Foundation.Modal.Logic.WellKnown

namespace LO.Modal.Logic

open Formula
open Entailment
open Kripke

theorem K_ssubset_KH : Logic.K ⊂ Logic.KH := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.KH ⊢! φ ∧ ¬FrameClass.all ⊧ φ by simpa [K.eq_AllKripkeFrameClass_Logic];
    use (Axioms.H (.atom 0));
    constructor;
    . exact axiomH!;
    . apply Kripke.not_validOnFrameClass_of_exists_model_world;
      use ⟨⟨Fin 1, λ x y => True⟩, λ w _ => False⟩, 0;
      simp [Satisfies, Semantics.Realize];
      constructor <;> tauto;
instance : ProperSublogic Logic.K Logic.KH := ⟨K_ssubset_KH⟩

theorem KH_ssubset_GL : Logic.KH ⊂ Logic.GL := by
  constructor;
  . exact Hilbert.weakerThan_of_dominate_axioms (by simp) |>.subset;
  . suffices ∃ φ, Hilbert.GL ⊢! φ ∧ ¬Hilbert.KH ⊢! φ by simpa;
    use (Axioms.Four (.atom 0));
    constructor;
    . exact axiomFour!;
    . exact KH_unprov_axiomFour;
instance : ProperSublogic Logic.KH Logic.GL := ⟨KH_ssubset_GL⟩

end LO.Modal.Logic

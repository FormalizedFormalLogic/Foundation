import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.Kripke.Logic.Int


namespace LO.Propositional

namespace Logic

class Superintuitionistic (L : Logic) where
  subset_Int : Logic.Int ⊆ L
  mdp_closed {φ ψ} : φ ➝ ψ ∈ L → φ ∈ L → ψ ∈ L
  subst_closed {φ} : φ ∈ L → ∀ s, φ⟦s⟧ ∈ L

end Logic


namespace Hilbert

open Entailment

variable {H : Hilbert ℕ}

protected instance superintuitionistic [H.HasEFQ] : (H.logic).Superintuitionistic where
  subset_Int := by
    intro φ hφ;
    induction hφ using Hilbert.Deduction.rec! with
    | maxm h =>
      rcases (by simpa using h) with ⟨s, rfl⟩; simp;
    | mdp ihφψ ihφ => exact mdp! ihφψ ihφ;
    | _ => simp;
  mdp_closed := by
    intro φ ψ hφψ hφ;
    exact hφψ ⨀ hφ;
  subst_closed := by
    intro φ hφ s;
    exact Hilbert.Deduction.subst! s hφ;

end Hilbert

instance : (Logic.Int).Superintuitionistic := Hilbert.superintuitionistic

namespace Logic

variable {L : Logic} [L.Superintuitionistic] [L.Consistent]

lemma no_bot : ¬(⊥ ∈ L) := by
  intro hbot;
  suffices ∀ φ, φ ∈ L by
    apply @Consistent.consis L _;
    exact Set.eq_univ_iff_forall.mpr this;
  intro φ;
  apply @Superintuitionistic.mdp_closed L _ ⊥ φ ?_ hbot;
  apply Superintuitionistic.subset_Int;
  simp;

end Logic

end LO.Propositional

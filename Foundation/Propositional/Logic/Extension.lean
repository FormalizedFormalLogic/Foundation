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

end LO.Propositional

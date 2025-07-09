import Foundation.Modal.Hilbert.Minimal.Basic
import Foundation.Modal.Hilbert.Normal.Basic


namespace LO.Modal

open LO.Modal.Entailment

instance : Modal.K ≊ 𝐄𝐌𝐂𝐍 := by
  apply Entailment.Equiv.iff.mpr;
  intro φ;
  suffices Hilbert.K ⊢! φ ↔ Hilbert.EMCN ⊢! φ by
    simpa [Entailment.theory, Set.mem_setOf_eq];
  constructor;
  . intro h;
    induction h using Hilbert.Normal.rec! with
    | mdp ihφψ ihφ => apply ihφψ ⨀ ihφ;
    | nec ihφ => apply Entailment.nec! ihφ;
    | axm s h => rcases h with rfl; simp;
    | imply₁ | imply₂ | ec => simp;
  . intro h;
    induction h using Hilbert.WithRE.rec! with
    | mdp ihφψ ihφ => apply ihφψ ⨀ ihφ;
    | re h => apply re! h;
    | axm s h =>
      rcases h with (rfl | rfl | rfl);
      . simp;
      . simp;
      . exact boxverum!;
    | _ => simp;

end LO.Modal

import Foundation.ProvabilityLogic.Interpretation

namespace LO.ProvabilityLogic

open Entailment
open Modal
open Modal.Hilbert
open FirstOrder
open ProvabilityPredicate

variable {L : FirstOrder.Language} [Semiterm.Operator.GoedelNumber L (Sentence L)]
         [L.DecidableEq]
         {T U : FirstOrder.Theory L} [Diagonalization T]  [T ⪯ U]
         {𝔅 : ProvabilityPredicate T U} [𝔅.HBL]

lemma GL.arithmetical_soundness (h : Hilbert.GL ⊢! A) {f : Realization L} : U ⊢!. f.interpret 𝔅 A := by
  induction h using Hilbert.Normal.rec! with
  | axm _ hp =>
    rcases hp with (⟨_, rfl⟩ | ⟨_, rfl⟩)
    . exact D2_shift;
    . exact FLT_shift;
  | nec ihp => exact D1_shift ihp;
  | mdp ihpq ihp => exact ihpq ⨀ ihp;
  | imply₁ => exact imply₁!;
  | imply₂ => exact imply₂!;
  | ec => exact CCCOCOC!;

end LO.ProvabilityLogic

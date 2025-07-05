import Foundation.ProvabilityLogic.Interpretation

namespace LO.ProvabilityLogic

open Entailment
open Modal
open Modal.Hilbert
open FirstOrder
open ProvabilityPredicate

variable {L : FirstOrder.Language} [Semiterm.Operator.GoedelNumber L (Sentence L)]
         [L.DecidableEq]
         {T U : FirstOrder.Theory L} [T ⪯ U]
         {𝔅 : ProvabilityPredicate T U}

lemma N.arithmetical_soundness (h : Logic.N ⊢! A) {f : Realization L} : U ⊢!. f.interpret 𝔅 A := by
  induction h with
  | maxm hp => simp at hp;
  | nec ihp => exact D1_shift ihp;
  | mdp ihpq ihp => exact ihpq ⨀ ihp;
  | imply₁ => exact imply₁!;
  | imply₂ => exact imply₂!;
  | ec => exact CCCOCOC!;

end LO.ProvabilityLogic

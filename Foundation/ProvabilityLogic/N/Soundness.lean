import Foundation.ProvabilityLogic.Interpretation

namespace LO.ProvabilityLogic

open Entailment
open Modal
open Modal.Hilbert
open FirstOrder
open Provability

variable {L : FirstOrder.Language} [L.ReferenceableBy L]
         [L.DecidableEq]
         {T U : FirstOrder.Theory L} [T ⪯ U]
         {𝔅 : Provability T U}

lemma N.arithmetical_soundness (h : Hilbert.N ⊢! A) {f : Realization 𝔅} : U ⊢!. f A := by
  induction h using Hilbert.Normal.rec! with
  | axm _ hp => simp at hp
  | nec ihp => exact D1_shift ihp
  | mdp ihpq ihp => exact ihpq ⨀ ihp
  | imply₁ => exact imply₁!
  | imply₂ => exact imply₂!
  | ec => exact CCCOCOC!

end LO.ProvabilityLogic

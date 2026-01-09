module
import Foundation.ProvabilityLogic.Realization
import Foundation.Modal.Logic.GLPlusBoxBot.Basic
import Foundation.ProvabilityLogic.Height

namespace LO.ProvabilityLogic

open Entailment
open Modal
open Modal.Hilbert
open FirstOrder
open Provability

variable {L : FirstOrder.Language} [L.ReferenceableBy L]
         [L.DecidableEq]
         {T U : FirstOrder.Theory L} [Diagonalization T]  [T ⪯ U]
         {𝔅 : Provability T U} [𝔅.HBL]

lemma GL.arithmetical_soundness (h : Modal.GL ⊢ A) {f : Realization 𝔅} : U ⊢ f A := by
  induction h using Hilbert.Normal.rec! with
  | axm _ hp =>
    rcases hp with (⟨_, rfl⟩ | ⟨_, rfl⟩)
    . exact D2_shift;
    . exact FLT_shift;
  | nec ihp => exact D1_shift ihp;
  | mdp ihpq ihp => exact ihpq ⨀ ihp;
  | _ => dsimp [Realization.interpret]; cl_prover;

open Classical

theorem GLPlusBoxBot.arithmetical_soundness
    (hA : Modal.GLPlusBoxBot 𝔅.height ⊢ A)
    (f : Realization 𝔅) : U ⊢ f A := by
  cases h : 𝔅.height
  case _ =>
    exact GL.arithmetical_soundness (by simpa [h] using hA)
  case _ n =>
    have : Modal.GLPlusBoxBot n ⊢ A := by simpa [h] using hA
    have : Modal.GL ⊢ □^[n]⊥ ➝ A := iff_provable_GLPlusBoxBot_provable_GL.mp this
    have : U ⊢ f (□^[n]⊥ ➝ A) := GL.arithmetical_soundness this;
    have : U ⊢ 𝔅^[n] ⊥ ➝ f A := by simpa using (Realization.interpret.def_boxItr (f := f) n (A := ⊥)) ▸ this;
    exact this ⨀ (Provability.height_le_iff_boxBot.mp (by simp [h]))

end LO.ProvabilityLogic

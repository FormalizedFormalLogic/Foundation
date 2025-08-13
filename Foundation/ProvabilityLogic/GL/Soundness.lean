import Foundation.ProvabilityLogic.Interpretation
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

lemma GL.arithmetical_soundness (h : Modal.GL ⊢! A) {f : Realization 𝔅} : U ⊢!. f A := by
  replace h := Normal.iff_logic_provable_provable.mp h;
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

open Classical

theorem GLBoxBot.arithmetical_soundness
    (hA : Modal.GLPlusBoxBot 𝔅.height.toWithTop ⊢! A)
    (f : Realization 𝔅) : U ⊢!. f A := by
  cases h : 𝔅.height using PartENat.casesOn
  case _ =>
    exact GL.arithmetical_soundness (by simpa [h] using hA)
  case _ n =>
    have : Modal.GLPlusBoxBot n ⊢! A := by simpa [h] using hA
    have : Hilbert.GL ⊢! □^[n]⊥ ➝ A := by simpa using iff_provable_GLBB_provable_GL.mp this
    have : U ⊢!. f (□^[n]⊥ ➝ A) := GL.arithmetical_soundness (f := f) (by simpa using this)
    have : U ⊢!. 𝔅^[n] ⊥ ➝ f A := by
      simpa [Realization.interpret_imp_def, Realization.interpret_boxItr_def] using this
    exact this ⨀ (Provability.height_le_iff_boxDot.mp (by simp [h]))

end LO.ProvabilityLogic

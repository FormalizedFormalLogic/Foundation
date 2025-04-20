import Foundation.ProvabilityLogic.Basic

namespace LO.ProvabilityLogic

open Entailment
open Modal
open Modal.Hilbert
open FirstOrder FirstOrder.DerivabilityCondition
open ProvabilityPredicate

variable {α : Type u}
         {L : FirstOrder.Language} [Semiterm.Operator.GoedelNumber L (Sentence L)]
         [L.DecidableEq]
         {T U : FirstOrder.Theory L} [T ⪯ U]
         {𝔅 : ProvabilityPredicate T U}

lemma arithmetical_soundness_N (h : (Hilbert.N) ⊢! φ) : ∀ {f : Realization L}, U ⊢!. (f.interpret 𝔅 φ) := by
  intro f;
  induction h using Hilbert.Deduction.rec! with
  | maxm hp => simp at hp;
  | nec ihp => exact D1_shift ihp;
  | mdp ihpq ihp => exact ihpq ⨀ ihp;
  | imply₁ => exact imply₁!;
  | imply₂ => exact imply₂!;
  | ec => exact CCCOCOC!;


lemma arithmetical_soundness_GL [Diagonalization T] [𝔅.HBL] (h : (Hilbert.GL) ⊢! φ) : ∀ {f : Realization L}, U ⊢!. (f.interpret 𝔅 φ) := by
  intro f;
  induction h using Hilbert.Deduction.rec! with
  | maxm hp =>
    rcases (by simpa using hp) with (⟨_, rfl⟩ | ⟨_, rfl⟩)
    . exact D2_shift;
    . exact FLT_shift;
  | nec ihp => exact D1_shift ihp;
  | mdp ihpq ihp => exact ihpq ⨀ ihp;
  | imply₁ => exact imply₁!;
  | imply₂ => exact imply₂!;
  | ec => exact CCCOCOC!;

instance {T : Theory ℒₒᵣ} [𝐈𝚺₁ ⪯ T] [T.Delta1Definable] : ArithmeticalSound (Logic.GL) (T.standardDP T) := ⟨arithmetical_soundness_GL⟩

end LO.ProvabilityLogic

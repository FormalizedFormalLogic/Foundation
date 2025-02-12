import Incompleteness.Arith.DC
import Incompleteness.DC.Basic
import Foundation.Modal.Logic.WellKnown

namespace LO

open LO.FirstOrder LO.FirstOrder.DerivabilityCondition
open LO.Modal
open LO.Modal.Hilbert

variable {α : Type u}
variable [Semiterm.Operator.GoedelNumber L (Sentence L)]
         {T U : Theory L}


namespace ProvabilityLogic

/-- Mapping modal prop vars to first-order sentence -/
def Realization (L) := ℕ → FirstOrder.Sentence L

/-- Mapping modal formulae to first-order sentence -/
def Realization.interpret
  {T U : FirstOrder.Theory L}
  (f : Realization L) (𝔅 : ProvabilityPredicate T U) : Formula ℕ → FirstOrder.Sentence L
  | .atom a => f a
  | □φ => 𝔅 (f.interpret 𝔅 φ)
  | ⊥ => ⊥
  | φ ➝ ψ => (f.interpret 𝔅 φ) ➝ (f.interpret 𝔅 ψ)

variable [Semiterm.Operator.GoedelNumber L (Sentence L)]

class ArithmeticalSound (Λ : Modal.Logic) (𝔅 : ProvabilityPredicate T U) where
  sound : ∀ {φ}, (φ ∈ Λ) → (∀ {f : Realization L}, U ⊢!. (f.interpret 𝔅 φ))

class ArithmeticalComplete (Λ : Modal.Logic) (𝔅 : ProvabilityPredicate T U) where
  complete : ∀ {φ}, (∀ {f : Realization L}, U ⊢!. (f.interpret 𝔅 φ)) → (φ ∈ Λ)

section ArithmeticalSoundness

open Entailment
open Modal
open ProvabilityPredicate

variable {L : FirstOrder.Language} [Semiterm.Operator.GoedelNumber L (Sentence L)]
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
  | ec => exact elim_contra_neg!;


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
  | ec => exact elim_contra_neg!;

end ArithmeticalSoundness


section

instance (T : Theory ℒₒᵣ) [𝐈𝚺₁ ⪯ T] [T.Delta1Definable] : ArithmeticalSound (Logic.GL) (T.standardDP T) := ⟨arithmetical_soundness_GL⟩

end


end LO.ProvabilityLogic

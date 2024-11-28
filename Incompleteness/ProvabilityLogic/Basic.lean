import Incompleteness.Arith.DC
import Incompleteness.DC.Basic
import Foundation.Modal.Hilbert

namespace LO

open LO.FirstOrder LO.FirstOrder.DerivabilityCondition
open LO.Modal
open LO.Modal.Hilbert

variable {α : Type u}
variable [Semiterm.Operator.GoedelNumber L (Sentence L)]
         {T U : Theory L}


namespace ProvabilityLogic

/-- Mapping modal prop vars to first-order sentence -/
def Realization (α : Type u) (L) := α → FirstOrder.Sentence L

/-- Mapping modal formulae to first-order sentence -/
def Realization.interpret
  {T U : FirstOrder.Theory L}
  (f : Realization α L) (𝔅 : ProvabilityPredicate T U) : Formula α → FirstOrder.Sentence L
  | .atom a => f a
  | □φ => 𝔅 (f.interpret 𝔅 φ)
  | ⊥ => ⊥
  | φ ➝ ψ => (f.interpret 𝔅 φ) ➝ (f.interpret 𝔅 ψ)

variable [Semiterm.Operator.GoedelNumber L (Sentence L)]

class ArithmeticalSound (Λ : Hilbert α) (𝔅 : ProvabilityPredicate T U) where
  sound : ∀ {φ}, (Λ ⊢! φ) → (∀ {f : Realization α L}, U ⊢!. (f.interpret 𝔅 φ))

class ArithmeticalComplete (Λ : Hilbert α) (𝔅 : ProvabilityPredicate T U) where
  complete : ∀ {φ}, (∀ {f : Realization α L}, U ⊢!. (f.interpret 𝔅 φ)) → (Λ ⊢! φ)


section ArithmeticalSoundness

open System
open ProvabilityPredicate

variable {L : FirstOrder.Language} [Semiterm.Operator.GoedelNumber L (Sentence L)]
         [L.DecidableEq]
         {T U : FirstOrder.Theory L} [T ≼ U]
         {𝔅 : ProvabilityPredicate T U}

lemma arithmetical_soundness_N (h : (Hilbert.N α) ⊢! φ) : ∀ {f : Realization α L}, U ⊢!. (f.interpret 𝔅 φ) := by
  intro f;
  induction h using Deduction.inducition_with_necOnly! with
  | hMaxm hp => simp at hp;
  | hNec ihp => exact D1_shift ihp;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hImply₁ => exact imply₁!;
  | hImply₂ => exact imply₂!;
  | hElimContra => exact elim_contra_neg!;


lemma arithmetical_soundness_GL [Diagonalization T] [𝔅.HBL] (h : (Hilbert.GL α) ⊢! φ) : ∀ {f : Realization α L}, U ⊢!. (f.interpret 𝔅 φ) := by
  intro f;
  induction h using Deduction.inducition_with_necOnly! with
  | hMaxm hp =>
    rcases hp with (⟨_, _, rfl⟩ | ⟨_, rfl⟩)
    . exact D2_shift;
    . exact FLT_shift;
  | hNec ihp => exact D1_shift ihp;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hImply₁ => exact imply₁!;
  | hImply₂ => exact imply₂!;
  | hElimContra => exact elim_contra_neg!;

end ArithmeticalSoundness


section

instance (T : Theory ℒₒᵣ) [𝐈𝚺₁ ≼ T] [T.Delta1Definable] : ArithmeticalSound (Hilbert.GL α) (T.standardDP T) := ⟨arithmetical_soundness_GL⟩

end


end LO.ProvabilityLogic

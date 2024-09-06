import Incompleteness.Arith.DC
import Incompleteness.DC.Basic
import Logic.Modal.Hilbert

namespace LO

open LO.FirstOrder LO.FirstOrder.DerivabilityCondition
open LO.Modal

variable {α : Type u} [DecidableEq α]
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
  | □p => 𝔅 (f.interpret 𝔅 p)
  | ⊥ => ⊥
  | p ⟶ q => (f.interpret 𝔅 p) ⟶ (f.interpret 𝔅 q)

variable [Semiterm.Operator.GoedelNumber L (Sentence L)]

class ArithmeticalSound (Λ : Hilbert α) (𝔅 : ProvabilityPredicate T U) where
  sound : ∀ {p}, (Λ ⊢! p) → (∀ {f : Realization α L}, U ⊢!. (f.interpret 𝔅 p))

class ArithmeticalComplete (Λ : Hilbert α) (𝔅 : ProvabilityPredicate T U) where
  complete : ∀ {p}, (∀ {f : Realization α L}, U ⊢!. (f.interpret 𝔅 p)) → (Λ ⊢! p)


section ArithmeticalSoundness

open System
open ProvabilityPredicate

variable {L : FirstOrder.Language} [Semiterm.Operator.GoedelNumber L (Sentence L)]
         [DecidableEq (Sentence L)]
         {T U : FirstOrder.Theory L} [T ≼ U] [Diagonalization T]
         {𝔅 : ProvabilityPredicate T U}

lemma arithmetical_soundness_N (h : 𝐍 ⊢! p) : ∀ {f : Realization α L}, U ⊢!. (f.interpret 𝔅 p) := by
  intro f;
  induction h using Deduction.inducition_with_necOnly! with
  | hMaxm hp => simp at hp;
  | hNec ihp => exact D1_shift ihp;
  | hMdp ihpq ihp =>
    simp only [Realization.interpret] at ihpq;
    exact ihpq ⨀ ihp;
  | _ => dsimp [Realization.interpret]; trivial;

lemma arithmetical_soundness_GL [𝔅.HBL] (h : 𝐆𝐋 ⊢! p) : ∀ {f : Realization α L}, U ⊢!. (f.interpret 𝔅 p) := by
  intro f;
  induction h using Deduction.inducition_with_necOnly! with
  | hMaxm hp =>
    rcases hp with (⟨_, _, rfl⟩ | ⟨_, rfl⟩)
    . exact D2_shift;
    . exact FLT_shift;
  | hNec ihp => exact D1_shift ihp;
  | hMdp ihpq ihp =>
    simp [Realization.interpret] at ihpq;
    exact ihpq ⨀ ihp;
  | _ => dsimp [Realization.interpret]; trivial;

end ArithmeticalSoundness


section

instance (T : Theory ℒₒᵣ) [𝐈𝚺₁ ≼ T] [T.Delta1Definable] : ArithmeticalSound (𝐆𝐋 : Hilbert α) (T.standardDP T) := ⟨arithmetical_soundness_GL⟩

end


end LO.ProvabilityLogic

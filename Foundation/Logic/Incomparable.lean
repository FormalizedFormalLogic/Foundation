-- This file need to be moved to `Entailment`
import Foundation.Logic.Entailment


namespace LO.Entailment

variable {F : Type u_1} {S : Type u_2} {T : Type u_3}
         [Entailment F S] [Entailment F T]
         {𝓢 : S} {𝓣 : T}

class Incomparable (𝓢 : S) (𝓣 : T) where
  notWT₁ : ¬𝓢 ⪯ 𝓣
  notWT₂ : ¬𝓣 ⪯ 𝓢

lemma Incomparable.of_unprovable
  (h₁ : ∃ φ, 𝓢 ⊢! φ ∧ 𝓣 ⊬ φ)
  (h₂ : ∃ ψ, 𝓣 ⊢! ψ ∧ 𝓢 ⊬ ψ)
  : Incomparable (𝓢 : S) (𝓣 : T) := by
  constructor <;>
  . apply Entailment.not_weakerThan_iff.mpr;
    assumption;

end LO.Entailment

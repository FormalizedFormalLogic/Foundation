import Foundation.FirstOrder.Bootstrapping.WitnessComparison
import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition
import Foundation.FirstOrder.Bootstrapping.Consistency

namespace LO.FirstOrder

open FirstOrder Arithmetic
open PeanoMinus ISigma0 ISigma1 Bootstrapping Derivation

namespace Theory

variable {V : Type*} [ORingStructure V] [V ⊧ₘ* 𝗜𝚺₁]
variable {L : Language} [L.Encodable] [L.LORDefinable]

variable {T U : Theory L} [T.Δ₁] [U.Δ₁]

/-- Provability with restriction of proof-length -/
def RestrictedProvable (T : Theory L) [T.Δ₁] (φ : V) := ∃ d ≤ 2, T.Proof d φ

noncomputable def restrictedProvable : 𝚺₁.Semisentence 1 := .mkSigma “φ. ∃ d, d ≤ 2 ∧ !T.proof.sigma d φ”

noncomputable abbrev restrictedProvabilityPred (σ : Sentence L) : Sentence ℒₒᵣ := T.restrictedProvable.val/[⌜σ⌝]

instance RestrictedProvable.defined : 𝚺₁-Predicate[V] T.RestrictedProvable via T.restrictedProvable where
  defined {φ} := by simp [Theory.restrictedProvable, Theory.RestrictedProvable];

noncomputable abbrev restrictedGödel (T : Theory L) [T.Δ₁] : Sentence ℒₒᵣ := fixedpoint (∼T.restrictedProvable)

end Theory


namespace Arithmetic

variable {T U : ArithmeticTheory} [T.Δ₁] [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

end Arithmetic


end LO.FirstOrder

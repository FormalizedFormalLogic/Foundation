import Foundation.FirstOrder.Internal.FixedPoint
import Foundation.Meta.ClProver

namespace LO.ISigma1

open FirstOrder Entailment

variable {T : Theory ℒₒᵣ} [𝐈𝚺₁ ⪯ T] [Entailment.Consistent T]

/--
  There is no predicate `τ`, s.t. for any sentence `σ`, `σ` is provable in `T` iff `τ/[⌜σ⌝]` is so.
-/
lemma not_exists_tarski_predicate : ¬∃ τ : Semisentence ℒₒᵣ 1, ∀ σ, T ⊢!. σ ⭤ τ/[⌜σ⌝] := by
  rintro ⟨τ, hτ⟩
  apply Entailment.Consistent.not_bot (𝓢 := T.toAxiom)
  . infer_instance
  . have h₁ : T ⊢!. fixedpoint (∼τ) ⭤ τ/[⌜fixedpoint (∼τ)⌝] := by simpa using hτ $ fixedpoint “x. ¬!τ x”;
    have h₂ : T ⊢!. fixedpoint (∼τ) ⭤ ∼τ/[⌜fixedpoint (∼τ)⌝] := by simpa using diagonal (T := T) “x. ¬!τ x”
    cl_prover [h₁, h₂]

end LO.ISigma1


namespace LO.FirstOrderTrueArith

open FirstOrder Arithmetic

lemma provable_iff₀ {σ : Sentence ℒₒᵣ} : 𝐓𝐀 ⊢!. σ ↔ ℕ ⊧ₘ₀ σ := by
  apply Iff.trans ?_ $ provable_iff (φ := σ)
  exact Axiom.provable_iff

end LO.FirstOrderTrueArith



namespace LO.FirstOrder.Arithmetic

/--
  Tarski's Undefinability of Truth Theorem.
-/
theorem undefinability_of_truth : ¬∃ τ : Semisentence ℒₒᵣ 1, ∀ σ : Sentence ℒₒᵣ, ℕ ⊧ₘ₀ σ ↔ ℕ ⊧ₘ₀ τ/[⌜σ⌝] := by
  have := ISigma1.not_exists_tarski_predicate (T := 𝐓𝐀)
  contrapose! this
  obtain ⟨τ, hτ⟩ := this
  use τ
  intro σ
  apply FirstOrderTrueArith.provable_iff₀.mpr
  simpa using hτ σ

end LO.FirstOrder.Arithmetic

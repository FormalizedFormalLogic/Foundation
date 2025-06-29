import Foundation.FirstOrder.Incompleteness.First
import Foundation.Meta.ClProver

namespace LO

open LO.Entailment.Context
open FirstOrder Arith R0 PeanoMinus IOpen ISigma0 ISigma1 Metamath

lemma R0.interpolant (T : Theory ℒₒᵣ) [𝐑₀ ⪯ T] [Sigma1Sound T] [T.Delta1Definable]
  (h₁ : T ⊢! φ ➝ ψ) (h₂ : T ⊬ ψ ➝ φ)
  : ∃ ξ, (T ⊢! φ ➝ ξ ∧ T ⊬ ξ ➝ φ) ∧ (T ⊢! ξ ➝ ψ ∧ T ⊬ ψ ➝ ξ) := by
  have : ¬Entailment.Complete (T + {ψ, ∼φ}) := @R0.goedel_first_incompleteness _ ?_ ?_ ?_;
  . obtain ⟨ρ, hρ⟩ := Entailment.incomplete_iff_exists_undecidable.mp this;
    use φ ⋎ (ψ ⋏ ∼ρ);
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩;
    . cl_prover;
    . by_contra hC;
      apply hρ.1;
      suffices T ⊢! ψ ➝ ∼φ ➝ ρ by
        sorry;
      cl_prover [h₁, hC];
    . cl_prover [h₁];
    . by_contra hC;
      apply hρ.2;
      suffices T ⊢! ψ ➝ ∼φ ➝ ∼ρ by
        sorry;
      cl_prover [h₁, hC];
  . calc
    _ ⪯ T           := by assumption;
    _ ⪯ T + {ψ, ∼φ} := by sorry;
  . sorry;
  . apply Theory.Delta1Definable.add;
    . assumption;
    . sorry;

end LO

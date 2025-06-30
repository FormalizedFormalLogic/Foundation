import Foundation.FirstOrder.Incompleteness.First
import Foundation.Meta.ClProver
import Foundation.Logic.LindenbaumAlgebra

namespace LO

open LO.Entailment.Context
open Entailment LindenbaumAlgebra
open FirstOrder Arith R0 PeanoMinus IOpen ISigma0 ISigma1 Metamath

/-- Lindenbuam algebra of `𝐑₀`-extension theory satisfies G1 is dense. -/
lemma R0.dense (T : Theory ℒₒᵣ) [𝐑₀ ⪯ T] [Sigma1Sound T] [T.Delta1Definable] {φ ψ : LindenbaumAlgebra T}
  (h : φ < ψ) : ∃ ξ, φ < ξ ∧ ξ < ψ := by
  obtain ⟨φ, rfl⟩ := Quotient.exists_rep φ;
  obtain ⟨ψ, rfl⟩ := Quotient.exists_rep ψ;

  have h₁ : T ⊢! φ ➝ ψ := LindenbaumAlgebra.le_def _ |>.mp $ le_of_lt h;
  have h₂ : T ⊬ ψ ➝ φ  := LindenbaumAlgebra.le_def _ |>.not.mp $ not_le_of_lt h;

  have : ¬Entailment.Complete (T + {ψ, ∼φ}) := @R0.goedel_first_incompleteness _ ?_ ?_ ?_;
  . obtain ⟨ρ, hρ⟩ := Entailment.incomplete_iff_exists_undecidable.mp this;
    use ⟦φ ⋎ (ψ ⋏ ∼ρ)⟧;
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩;
    . apply LindenbaumAlgebra.le_def _ |>.mpr;
      cl_prover;
    . apply LindenbaumAlgebra.le_def _ |>.not.mpr;
      by_contra hC;
      apply hρ.1;
      suffices T ⊢! ψ ➝ ∼φ ➝ ρ by
        sorry;
      cl_prover [h₁, hC];
    . apply LindenbaumAlgebra.le_def _ |>.mpr;
      cl_prover [h₁];
    . apply LindenbaumAlgebra.le_def _ |>.not.mpr;
      by_contra hC;
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

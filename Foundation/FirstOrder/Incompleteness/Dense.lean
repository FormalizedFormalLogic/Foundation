import Foundation.FirstOrder.Incompleteness.First
import Foundation.Meta.ClProver
import Foundation.Logic.LindenbaumAlgebra

namespace LO


namespace Entailment

variable {F S : Type*} [DecidableEq F] [LogicalConnective F] [Entailment F S] [Collection F S] [Deduction S]
         {𝓢 : S} [Entailment.Cl 𝓢]

lemma consistent_cons_of_unprovable_neg (h : 𝓢 ⊬ ∼φ) : Consistent (cons φ 𝓢) := by
  apply consistent_iff_exists_unprovable.mpr;
  use ⊥;
  apply deduction_iff.not.mpr;
  contrapose! h;
  simp only [not_not];
  cl_prover [h];

lemma consistent_cons_of_unprovable (h : 𝓢 ⊬ φ) : Consistent (cons (∼φ) 𝓢) := by
  apply consistent_cons_of_unprovable_neg;
  contrapose! h;
  simp_all only [not_not];
  cl_prover [h];

end Entailment


namespace Entailment.LindenbaumAlgebra

open Entailment LindenbaumAlgebra

variable {F S : Type*} [DecidableEq F] [LogicalConnective F] [Entailment F S] [Collection F S] [Deduction S]
         (𝓢 : S) [Entailment.Cl 𝓢]

lemma dense_of_finite_extend_incomplete
  (hE : ∀ φ : F, Entailment.Consistent (cons φ 𝓢) → ¬Entailment.Complete (cons φ 𝓢))
  (h : φ < ψ) : ∃ ξ : LindenbaumAlgebra 𝓢, φ < ξ ∧ ξ < ψ := by
  obtain ⟨φ, rfl⟩ := Quotient.exists_rep φ;
  obtain ⟨ψ, rfl⟩ := Quotient.exists_rep ψ;

  have h₁ : 𝓢 ⊢! φ ➝ ψ := le_def _ |>.mp $ le_of_lt h;
  have h₂ : 𝓢 ⊬  ψ ➝ φ := le_def _ |>.not.mp $ not_le_of_gt h;

  obtain ⟨ρ, hρ⟩ := Entailment.incomplete_iff_exists_undecidable.mp $ @hE (∼φ ⋏ ψ) $ by
    apply consistent_iff_exists_unprovable.mpr;
    use ⊥;
    apply deduction_iff.not.mpr;
    contrapose! h₂;
    simp only [not_not];
    cl_prover [h₂];
  use ⟦φ ⋎ (ψ ⋏ ∼ρ)⟧;
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩;
  . apply le_def _ |>.mpr;
    cl_prover;
  . apply le_def _ |>.not.mpr;
    by_contra! hC;
    apply hρ.1;
    apply deduction_iff.mpr;
    cl_prover [h₁, hC];
  . apply le_def _ |>.mpr;
    cl_prover [h₁];
  . apply le_def _ |>.not.mpr;
    by_contra hC;
    apply hρ.2;
    apply deduction_iff.mpr;
    cl_prover [h₁, hC];

end Entailment.LindenbaumAlgebra



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

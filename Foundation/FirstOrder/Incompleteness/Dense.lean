import Foundation.FirstOrder.Incompleteness.Second
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

open Entailment LindenbaumAlgebra FirstOrder

/-- Lindenbuam algebra of `𝐈𝚺₁`-extension theory satisfies G1 is dense. -/
lemma ISigma1.dense (T : Theory ℒₒᵣ) [𝐈𝚺₁ ⪯ T] [T.Δ₁] {φ ψ : LindenbaumAlgebra (T : Axiom ℒₒᵣ)} :
    φ < ψ → ∃ ξ, φ < ξ ∧ ξ < ψ := fun h ↦ by
  refine LindenbaumAlgebra.dense_of_finite_extend_incomplete (T : Axiom ℒₒᵣ) ?_ h
  intro σ con
  have : 𝐈𝚺₁ ⪯ insert ↑σ T := WeakerThan.trans (inferInstanceAs (𝐈𝚺₁ ⪯ T)) (Axiomatized.le_of_subset (by simp))
  have : Consistent (insert ↑σ T) := (Axiom.consistent_iff (L := ℒₒᵣ)).mp <| by simpa [-Axiom.consistent_iff] using con
  simpa using Arithmetic.incomplete' (insert ↑σ T)

instance (T : Theory ℒₒᵣ) [𝐈𝚺₁ ⪯ T] [T.Δ₁] : DenselyOrdered (LindenbaumAlgebra (T : Axiom ℒₒᵣ)) where
  dense _ _ := ISigma1.dense T

end LO

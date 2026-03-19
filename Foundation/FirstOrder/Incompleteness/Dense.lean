module

public import Foundation.FirstOrder.Incompleteness.GödelRosser
public import Foundation.Logic.LindenbaumAlgebra

@[expose] public section
namespace LO

namespace Entailment

variable {F S : Type*} [DecidableEq F] [LogicalConnective F] [Entailment S F] [AdjunctiveSet F S] [Deduction S]
         {𝓢 : S} [Entailment.Cl 𝓢]

lemma consistent_cons_of_unprovable_neg (h : 𝓢 ⊬ ∼φ) : Consistent (adjoin φ 𝓢) := by
  apply consistent_iff_exists_unprovable.mpr;
  use ⊥;
  apply deduction_iff.not.mpr;
  contrapose! h;
  cl_prover [h];

lemma consistent_cons_of_unprovable (h : 𝓢 ⊬ φ) : Consistent (adjoin (∼φ) 𝓢) := by
  apply consistent_cons_of_unprovable_neg;
  contrapose! h;
  cl_prover [h];

end Entailment

namespace Entailment.LindenbaumAlgebra

open Entailment LindenbaumAlgebra

variable {F S : Type*} [DecidableEq F] [LogicalConnective F] [Entailment S F] [AdjunctiveSet F S] [Deduction S]
         (𝓢 : S) [Entailment.Cl 𝓢]

lemma dense_of_finite_extend_incomplete
    (hE : ∀ φ : F, Consistent (adjoin φ 𝓢) → Incomplete (adjoin φ 𝓢))
    (h : φ < ψ) : ∃ ξ : LindenbaumAlgebra 𝓢, φ < ξ ∧ ξ < ψ := by
  obtain ⟨φ, rfl⟩ := Quotient.exists_rep φ;
  obtain ⟨ψ, rfl⟩ := Quotient.exists_rep ψ;
  have h₁ : 𝓢 ⊢ φ 🡒 ψ := le_def _ |>.mp $ le_of_lt h;
  have h₂ : 𝓢 ⊬  ψ 🡒 φ := le_def _ |>.not.mp $ not_le_of_gt h;
  obtain ⟨ρ, hρ⟩ := incomplete_def.mp $ @hE (∼φ ⋏ ψ) $ by
    apply consistent_iff_exists_unprovable.mpr;
    use ⊥;
    apply deduction_iff.not.mpr;
    contrapose! h₂;
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

/-- Lindenbuam algebra of `𝗜𝚺₁`-extension theory satisfies G1 is dense. -/
lemma FirstOrder.Arithmetic.dense (T : Theory ℒₒᵣ) [𝗜𝚺₁ ⪯ T] [T.Δ₁] {φ ψ : LindenbaumAlgebra T} :
    φ < ψ → ∃ ξ, φ < ξ ∧ ξ < ψ := fun h ↦ by
  refine LindenbaumAlgebra.dense_of_finite_extend_incomplete T ?_ h
  intro σ con
  have : 𝗜𝚺₁ ⪯ insert σ T := WeakerThan.trans (inferInstanceAs (𝗜𝚺₁ ⪯ T)) (Axiomatized.le_of_subset (by simp))
  simpa using Arithmetic.incomplete' (insert σ T)

instance (T : Theory ℒₒᵣ) [𝗜𝚺₁ ⪯ T] [T.Δ₁] : DenselyOrdered (LindenbaumAlgebra T) where
  dense _ _ := FirstOrder.Arithmetic.dense T

end LO

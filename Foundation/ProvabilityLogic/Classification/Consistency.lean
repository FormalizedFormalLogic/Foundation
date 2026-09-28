module

public import Foundation.ProvabilityLogic.Classification.Reflection

/-!
# The provability logic of `T` relative to `T + Con(U)`

If `U` extends `T` provably in `𝗜𝚺₁` and proves the local $\Sigma_1$ reflection principle of `T`,
and `T + Con(U)` is consistent, then the provability logic of `T` relative to `T + Con(U)` is `𝐀`.

## References

- [AB05, Example 63]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment FirstOrder FirstOrder.Arithmetic Formula LetterlessFormula

variable {α : Type*} {T U : ArithmeticTheory} [U.Δ₁] [𝗜𝚺₁ ⪯ T]

local instance : 𝗜𝚺₁ ⪯ T ∪ U.Con := (inferInstance : 𝗜𝚺₁ ⪯ T).trans inferInstance

variable [T.Δ₁]

lemma trace_provabilityLogic_add_con_eq_univ
    (hTU : ∀ σ, 𝗜𝚺₁ ⊢ T.standardProvability σ 🡒 U.standardProvability σ)
    (hU : U ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T) :
    (T.provabilityLogicRelativeTo (T ∪ U.Con) (α := α)).trace = .univ :=
  Set.eq_univ_of_forall fun n ↦ mem_trace_provabilityLogic_iff.mpr fun f ↦ by
    have h₁ : T ∪ U.Con ⊢ ∼U.standardProvability ⊥ := by_axm <| Set.mem_union_right _ rfl;
    have h₂ : T ∪ U.Con ⊢ _ :=
      WeakerThan.pbl <| provable_iterate_standardProvability_bot_imp hTU hU n;
    simp only [alpha, standardInterpret, interpret, interpret_boxItr];
    cl_prover [h₁, h₂];

lemma A_weakerThan_provabilityLogic_add_con
    (hTU : ∀ σ, 𝗜𝚺₁ ⊢ T.standardProvability σ 🡒 U.standardProvability σ)
    (hU : U ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T) :
    𝐀 ⪯ T.provabilityLogicRelativeTo (T ∪ U.Con) (α := α) :=
  A_weakerThan_provabilityLogic <| trace_provabilityLogic_add_con_eq_univ hTU hU

theorem provabilityLogic_add_con_eq_A
    (hTU : ∀ σ, 𝗜𝚺₁ ⊢ T.standardProvability σ 🡒 U.standardProvability σ)
    (hU : U ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T) (hC : Consistent (T ∪ U.Con)) :
    T.provabilityLogicRelativeTo (T ∪ U.Con) (α := α) = 𝐀 := by
  apply Logic.weakerThan_antisymm;
  · -- A logic strictly above `𝐀` would give `T ∪ Con(U)` the local `Σ1` reflection schema of `T`
    -- from its single `Π1` axiom `Con(U)`, which [AB05, Theorem 23] forbids.
    by_contra! h;
    obtain ⟨-, A, hAA, hAL⟩ :=
      strictlyWeakerThan_iff.mp ⟨A_weakerThan_provabilityLogic_add_con hTU hU, h⟩;
    have h₁ : T ∪ U.Con ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T :=
      provable_localReflectionOn_sigma1_of_mem_of_not_A
        (trace_provabilityLogic_add_con_eq_univ hTU hU) hAL hAA;
    rw [Set.union_singleton] at h₁ hC;
    exact (T.standardProvability.inconsistent_of_provable_localReflectionOn_insert
      (fun _ hσ ↦ by simpa using hσ) (by simp : ℬ[<, ℒₒᵣ].Hierarchy 𝚷 1 _) h₁).not_con hC;
  · exact A_weakerThan_provabilityLogic_add_con hTU hU;

end FFL.ProvabilityLogic

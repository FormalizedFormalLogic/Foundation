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

variable {α : Type*} {T U : ArithmeticTheory} [T.Δ₁] [U.Δ₁] [𝗜𝚺₁ ⪯ T]

lemma trace_provabilityLogic_add_con_eq_univ
    (hTU : ∀ σ, 𝗜𝚺₁ ⊢ T.standardProvability σ 🡒 U.standardProvability σ)
    (hU : U ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T) :
    (T.provabilityLogicRelativeTo (T ∪ U.Con) (α := α)).trace = .univ := by
  have : 𝗜𝚺₁ ⪯ T ∪ U.Con := (inferInstance : 𝗜𝚺₁ ⪯ T).trans <|
    WeakerThan.ofSubset Set.subset_union_left;
  apply Set.eq_univ_of_forall;
  intro n;
  apply mem_trace_provabilityLogic_iff.mpr;
  intro f;
  have h₁ : T ∪ U.Con ⊢ ∼U.standardProvability ⊥ := by_axm <| Set.mem_union_right _ rfl;
  have h₂ := WeakerThan.pbl (𝓣 := T ∪ U.Con) <|
    provable_iterate_standardProvability_bot_imp hTU hU n;
  simp only [alpha, standardInterpret, interpret, interpret_boxItr];
  cl_prover [h₁, h₂];

lemma A_weakerThan_provabilityLogic_add_con
    (hTU : ∀ σ, 𝗜𝚺₁ ⊢ T.standardProvability σ 🡒 U.standardProvability σ)
    (hU : U ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T) :
    𝐀 ⪯ T.provabilityLogicRelativeTo (T ∪ U.Con) (α := α) :=
  have : 𝗜𝚺₁ ⪯ T ∪ U.Con := (inferInstance : 𝗜𝚺₁ ⪯ T).trans <|
    WeakerThan.ofSubset Set.subset_union_left
  A_weakerThan_provabilityLogic (trace_provabilityLogic_add_con_eq_univ hTU hU)

theorem provabilityLogic_add_con_eq_A
    (hTU : ∀ σ, 𝗜𝚺₁ ⊢ T.standardProvability σ 🡒 U.standardProvability σ)
    (hU : U ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T) (hC : Consistent (T ∪ U.Con)) :
    T.provabilityLogicRelativeTo (T ∪ U.Con) (α := α) = 𝐀 := by
  have : 𝗜𝚺₁ ⪯ T ∪ U.Con := (inferInstance : 𝗜𝚺₁ ⪯ T).trans <|
    WeakerThan.ofSubset Set.subset_union_left;
  apply Logic.weakerThan_antisymm;
  · -- A logic strictly above `𝐀` would give `T ∪ Con(U)` the local `Σ1` reflection schema of `T`
    -- from its single `Π1` axiom `Con(U)`, which [AB05, Theorem 23] forbids.
    by_contra! h;
    obtain ⟨-, A, hAA, hAL⟩ := strictlyWeakerThan_iff.mp
      (⟨A_weakerThan_provabilityLogic_add_con hTU hU, h⟩ : 𝐀 ⪱ _);
    have h₁ : T ∪ U.Con ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T :=
      provable_localReflectionOn_sigma1_of_mem_of_not_A
        (trace_provabilityLogic_add_con_eq_univ hTU hU) hAL hAA;
    rw [Set.union_singleton] at h₁;
    exact (T.standardProvability.inconsistent_of_provable_localReflectionOn_insert
      (Γ := ℬ[<, ℒₒᵣ].Hierarchy 𝚷 1) (fun _ hσ ↦ by simpa using hσ) (by simp) h₁).not_con
      (Set.union_singleton ▸ hC);
  · exact A_weakerThan_provabilityLogic_add_con hTU hU;

end FFL.ProvabilityLogic

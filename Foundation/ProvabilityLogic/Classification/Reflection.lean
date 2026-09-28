module

public import Foundation.ProvabilityLogic.Classification.General
public import Foundation.FirstOrder.Incompleteness.Reflection.Local

/-!
# Provability logics under local reflection

If `U` proves the local $\Sigma_1$ reflection principle of `T`, the provability logic of `T`
relative to `U` has trace `ω` and contains `𝐃`; if `U` proves the full local reflection principle
of `T`, it contains `𝐒`.

## References

- [AB05]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment FirstOrder FirstOrder.Arithmetic Formula LetterlessFormula

variable {α : Type*} {T U : ArithmeticTheory} [T.Δ₁]

lemma alpha_mem_provabilityLogic_of_provable_localReflectionOn_Sigma1
    (h : U ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T) :
    ∀ n, alpha n ∈ T.provabilityLogicRelativeTo U (α := α) := by
  intro n f;
  simpa [alpha, standardInterpret, interpret, interpret_boxItr, Function.iterate_succ_apply'] using
    h ⟨_, hierarchy_iterate_standardProvability_bot n, rfl⟩

variable [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

lemma trace_provabilityLogic_eq_univ_of_provable_localReflectionOn_Sigma1
    (h : U ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T) :
    (T.provabilityLogicRelativeTo U (α := α)).trace = .univ := by
  apply Set.eq_univ_of_forall;
  intro n;
  exact
    mem_trace_provabilityLogic_iff.mpr <|
    alpha_mem_provabilityLogic_of_provable_localReflectionOn_Sigma1 h n

theorem D_weakerThan_provabilityLogic_of_provable_localReflectionOn_Sigma1
    (h : U ⊢* 𝗥𝗳𝗻[ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1] T) :
    𝐃 ⪯ T.provabilityLogicRelativeTo U (α := α) := by
  apply sumQuasiNormal_weakerThan_provabilityLogic;
  rintro _ (rfl | ⟨B, C, rfl⟩);
  · exact (A_weakerThan_provabilityLogic
      (trace_provabilityLogic_eq_univ_of_provable_localReflectionOn_Sigma1 h)).wk
      (Logic.A.neg_boxItr_bot (n := 1));
  · intro f;
    apply h;
    use f T (□B ⋎ □C);
    and_intros;
    · -- The goal is stated as set membership, which `simp` does not unfold on its own.
      change ℬ[<, ℒₒᵣ].Hierarchy 𝚺 1 _;
      simp [standardInterpret, interpret, standardProvability_def];
    · rfl;

theorem S_weakerThan_provabilityLogic_of_provable_localReflection
    (h : U ⊢* 𝗥𝗳𝗻[Set.univ] T) :
    𝐒 ⪯ T.provabilityLogicRelativeTo U (α := α) := by
  apply sumQuasiNormal_weakerThan_provabilityLogic;
  rintro _ ⟨C, rfl⟩ f;
  exact h ⟨_, trivial, rfl⟩

end FFL.ProvabilityLogic

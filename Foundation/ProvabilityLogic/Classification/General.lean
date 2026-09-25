module

public import Foundation.ProvabilityLogic.Classification.UnivTrace

/-!
# Classification of provability logics

The provability logic of `T` relative to `U` is one of `GLα X`, `GLβ⁻ X`, `D ∩ GLβ⁻ X`, and
`S ∩ GLβ⁻ X`, where `X` is its trace.

## References

- [AB05, Theorem 40]
- [Bek90, Assertion 6]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment FirstOrder Formula LetterlessFormula

variable {α : Type*} {T U : ArithmeticTheory} [T.Δ₁] {N : Set ℕ}

/-- `U` extended by the standard `T`-interpretations of `TBB n` for `n ∈ N`. -/
noncomputable def _root_.FFL.FirstOrder.ArithmeticTheory.addTBB
    (T U : ArithmeticTheory) [T.Δ₁] (N : Set ℕ) : ArithmeticTheory :=
  U ∪ (fun n ↦ (TBB n : LetterlessFormula).interpret ⟨Empty.elim⟩ T.standardProvability) '' N

lemma _root_.FFL.FirstOrder.ArithmeticTheory.weakerThan_addTBB : U ⪯ T.addTBB U N :=
  WeakerThan.ofSubset Set.subset_union_left

instance [𝗜𝚺₁ ⪯ U] : 𝗜𝚺₁ ⪯ T.addTBB U N :=
  (inferInstance : 𝗜𝚺₁ ⪯ U).trans ArithmeticTheory.weakerThan_addTBB

lemma provabilityLogic_subset_addTBB :
    (T.provabilityLogicRelativeTo U : Logic α) ⊆ T.provabilityLogicRelativeTo (T.addTBB U N) :=
  sorry

lemma TBB_mem_provabilityLogic_addTBB {n : ℕ} (hn : n ∈ N) :
    (TBB n : Formula α) ∈ T.provabilityLogicRelativeTo (T.addTBB U N) :=
  sorry

section

variable [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

lemma imp_mem_provabilityLogic_of_mem_addTBB (hN : N.Finite) {A : Formula α}
    (h : A ∈ T.provabilityLogicRelativeTo (T.addTBB U N)) :
    (⩕ n ∈ hN.toFinset, TBB n : LetterlessFormula).lift 🡒 A ∈ T.provabilityLogicRelativeTo U :=
  sorry

lemma trace_provabilityLogic_addTBB :
    (T.provabilityLogicRelativeTo
      (T.addTBB U (T.provabilityLogicRelativeTo U : Logic α).traceᶜ) : Logic α).trace = .univ :=
  sorry

variable (hL : (T.provabilityLogicRelativeTo U : Logic α).traceᶜ.Finite)

lemma provabilityLogic_addTBB_subset_S (h : (T.provabilityLogicRelativeTo U : Logic α) ⊆ 𝐒) :
    (T.provabilityLogicRelativeTo
      (T.addTBB U (T.provabilityLogicRelativeTo U : Logic α).traceᶜ) : Logic α) ⊆ 𝐒 :=
  sorry

lemma provabilityLogic_eq_inter_GLBetaMinus :
    (T.provabilityLogicRelativeTo U : Logic α) =
      T.provabilityLogicRelativeTo (T.addTBB U (T.provabilityLogicRelativeTo U : Logic α).traceᶜ) ∩
        𝐆𝐋β⁻ _ hL :=
  sorry

theorem provabilityLogic_eq_GLAlpha_or_eq_D_inter_or_eq_S_inter
    (h : (T.provabilityLogicRelativeTo U : Logic α) ⊆ 𝐒) :
    (T.provabilityLogicRelativeTo U : Logic α) =
        𝐆𝐋α (T.provabilityLogicRelativeTo U : Logic α).trace ∨
      (T.provabilityLogicRelativeTo U : Logic α) = 𝐃 ∩ 𝐆𝐋β⁻ _ hL ∨
      (T.provabilityLogicRelativeTo U : Logic α) = 𝐒 ∩ 𝐆𝐋β⁻ _ hL :=
  sorry

omit hL in
/-- The provability logic of `T` relative to `U` is one of `GLα X`, `GLβ⁻ X`, `D ∩ GLβ⁻ X`, and
`S ∩ GLβ⁻ X`, where `X` is its trace.

- [AB05, Theorem 40]
- [Bek90, Assertion 6]
-/
theorem provabilityLogic_classification :
    (T.provabilityLogicRelativeTo U : Logic α) =
        𝐆𝐋α (T.provabilityLogicRelativeTo U : Logic α).trace ∨
      ∃ hL : (T.provabilityLogicRelativeTo U : Logic α).traceᶜ.Finite,
        (T.provabilityLogicRelativeTo U : Logic α) = 𝐆𝐋β⁻ _ hL ∨
        (T.provabilityLogicRelativeTo U : Logic α) = 𝐃 ∩ 𝐆𝐋β⁻ _ hL ∨
        (T.provabilityLogicRelativeTo U : Logic α) = 𝐒 ∩ 𝐆𝐋β⁻ _ hL := by
  by_cases h₁ : (T.provabilityLogicRelativeTo U : Logic α).traceᶜ.Infinite;
  · exact .inl <| provabilityLogic_eq_GLAlpha h₁;
  have hL := Set.not_infinite.mp h₁;
  by_cases h₂ : (T.provabilityLogicRelativeTo U : Logic α) ⊆ 𝐒;
  · rcases provabilityLogic_eq_GLAlpha_or_eq_D_inter_or_eq_S_inter hL h₂ with h | h | h;
    · exact .inl h;
    · exact .inr ⟨hL, .inr <| .inl h⟩;
    · exact .inr ⟨hL, .inr <| .inr h⟩;
  · exact .inr ⟨_, .inl <| provabilityLogic_eq_GLBetaMinus h₂⟩;

end

end FFL.ProvabilityLogic

end

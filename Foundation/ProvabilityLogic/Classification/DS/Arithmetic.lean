module

public import Foundation.ProvabilityLogic.Classification.DS.Modal
public import Foundation.ProvabilityLogic.Classification.ProvabilityLogicTrace

/-!
# No provability logic of trace `ω` lies strictly between `𝐃` and `𝐒`

If the provability logic of `T` relative to `U` has trace `ω` and contains a formula outside `𝐃`,
then `U` proves the local reflection schema for `T`, so the logic contains `𝐒`.

## References

- [AB05, Lemma 56, Lemma 57, Corollary 58]
- [Bek90, Theorem 1, Assertion 1]
-/

@[expose] public section

namespace FFL.ProvabilityLogic

open Entailment FirstOrder Formula LetterlessFormula

variable {α : Type*} {T U : ArithmeticTheory} [T.Δ₁]

lemma LetterlessFormula.lift_mem_provabilityLogic_iff {β : Type*} {A : LetterlessFormula} :
    A.lift ∈ (T.provabilityLogicRelativeTo U : Logic α) ↔
      A.lift ∈ (T.provabilityLogicRelativeTo U : Logic β) := by
  constructor <;> intro h f <;> simpa only [standardInterpret, interpret_lift] using h ⟨fun _ ↦ ⊥⟩;

variable [𝗜𝚺₁ ⪯ T] [𝗜𝚺₁ ⪯ U]

/-- If the provability logic of `T` relative to `U` has trace `ω` and contains a formula outside
`𝐃`, then `U` proves `Pr_T(σ) 🡒 σ` for every sentence `σ`.

- [Bek90, Theorem 1]
- [AB05, Lemma 57]
-/
theorem provable_reflection_of_not_D
    (hT : (T.provabilityLogicRelativeTo U : Logic α).trace = .univ) {A : Formula α}
    (hA : A ∈ (T.provabilityLogicRelativeTo U : Logic α)) (hAD : 𝐃 ⊬ A)
    (σ : ArithmeticSentence) : U ⊢ T.standardProvability σ 🡒 σ := by
  sorry

/-- A provability logic of trace `ω` strictly containing `𝐃` contains `𝐒`.

- [Bek90, Assertion 1]
- [AB05, Lemma 56, Lemma 57]
-/
theorem S_subset_provabilityLogic
    (hT : (T.provabilityLogicRelativeTo U : Logic α).trace = .univ)
    (h : 𝐃 ⊂ (T.provabilityLogicRelativeTo U : Logic α)) :
    𝐒 ⊆ (T.provabilityLogicRelativeTo U : Logic α) := by
  sorry

/-- No provability logic of trace `ω` lies strictly between `𝐃` and `𝐒`.

- [AB05, Corollary 58]
-/
theorem not_D_ssubset_provabilityLogic_ssubset_S
    (hT : (T.provabilityLogicRelativeTo U : Logic α).trace = .univ) :
    ¬(𝐃 ⊂ (T.provabilityLogicRelativeTo U : Logic α) ∧
      (T.provabilityLogicRelativeTo U : Logic α) ⊂ 𝐒) := by
  sorry

end FFL.ProvabilityLogic

end

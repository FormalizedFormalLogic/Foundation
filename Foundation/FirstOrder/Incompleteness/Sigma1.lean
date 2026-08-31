module

public import Foundation.FirstOrder.Bootstrapping.Syntax.CraigTrick
public import Foundation.FirstOrder.Incompleteness.First

/-!
# Sigma-one definability and incompleteness
-/

@[expose] public section

namespace LO.FirstOrder.Arithmetic

open LO.Entailment

noncomputable instance (T : ArithmeticTheory) [T.«Σ₁»] [𝗥₀ ⪯ T] : 𝗥₀ ⪯ T.craig :=
  WeakerThan.trans (𝓣 := T) inferInstance (Theory.craig.original_weakerThan (T := T))

noncomputable instance (T : ArithmeticTheory) [T.«Σ₁»] [𝗜𝚺₁ ⪯ T] : 𝗜𝚺₁ ⪯ T.craig :=
  WeakerThan.trans (𝓣 := T) inferInstance (Theory.craig.original_weakerThan (T := T))

theorem incomplete_of_sigma1 (T : ArithmeticTheory) [T.«Σ₁»] [𝗥₀ ⪯ T]
    [T.SoundOnHierarchy 𝚺 1] : Incomplete T := by
  exact (Theory.craig_equiv (T := T)).symm.incomplete
    (@incomplete T.craig inferInstance inferInstance
      (ArithmeticTheory.SoundOn.of_weakerThan _ T T.craig))

theorem exists_true_but_unprovable_sentence_of_sigma1
    (T : ArithmeticTheory) [T.«Σ₁»] [𝗥₀ ⪯ T] [T.SoundOnHierarchy 𝚺 1] :
    ∃ δ : ArithmeticSentence, ℕ↓[ℒₒᵣ] ⊧ δ ∧ T ⊬ δ := by
  obtain ⟨δ, hδ⟩ := incomplete_def.mp (incomplete_of_sigma1 T);
  by_cases h : ℕ↓[ℒₒᵣ] ⊧ δ
  . use δ;
    and_intros;
    . exact h
    . exact hδ.1
  . use ∼δ;
    and_intros;
    . simpa
    . exact hδ.2

end LO.FirstOrder.Arithmetic

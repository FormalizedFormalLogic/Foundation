import Logic.FirstOrder.Incompleteness.Derivability.Theory
import Logic.FirstOrder.Incompleteness.Derivability.Conditions
import Logic.FirstOrder.Incompleteness.Derivability.FirstIncompleteness
import Logic.FirstOrder.Incompleteness.Derivability.SecondIncompleteness

namespace LO.FirstOrder.Arith.Incompleteness

open FirstOrder.Theory HasProvablePred

variable (T₀ T : Theory ℒₒᵣ) [SubTheory T₀ T]
variable [Diagonizable T Σ 1] [Diagonizable T Π 1]
variable
  [HasProvablePred T]
  [HasProvablePred.Definable.Sigma T 1]
  [∀ σ, SubTheory T₀ (T ∪ {σ})] -- TODO: remove this
  [Derivability1 T₀ T]
  [Derivability1 T T] -- TODO: remove this
  [Derivability2 T₀ T]
  [Derivability2 T T] -- TODO: remove this
  [FormalizedCompleteness T₀ T Σ 1]
  [FormalizedCompleteness T T Σ 1] -- TODO: remove this
  [FormalizedDeductionTheorem T₀ T]
  [∀ σ, Diagonizable (T ∪ {σ}) Π 1]
  [∀ σ, HasProvablePred (T ∪ {σ})]

open Derivability1 Derivability2 FormalizedCompleteness FormalizedDeductionTheorem

variable (σ)
  [Definable.Sigma (T ∪ {~σ}) 1]
  [Derivability1 (T ∪ {~σ}) (T ∪ {~σ})]
  [Derivability2 (T ∪ {~σ}) (T ∪ {~σ})]
  [FormalizedCompleteness (T ∪ {~σ}) (T ∪ {~σ}) Σ 1]

/-- Löb's Theorem *with* 2nd Incompleteness Theorem -/
theorem LoebTheorem
  [∀ σ, SubTheory T₀ (T ∪ {σ})] -- TODO: remove
  : (T ⊢! σ) ↔ (T ⊢! ((Pr[T] ⸢σ⸣) ⟶ σ)) := by
  apply Iff.intro;
  . intro H; exact imply_intro_trivial H;
  . intro H;
    have h₁ : T ⊢! ~σ ⟶ ~Pr[T] ⸢σ⸣ := imply_contra₀ H;
    have h₂ : T ∪ {~σ} ⊢! ~Pr[T] ⸢σ⸣ := deduction.mp h₁;
    have h₃ : T ∪ {~σ} ⊢! ~Pr[T] ⸢~σ ⟶ ⊥⸣ := MP (iff_mp (iff_contra (weakening $ @formalized_neg_def T _ (~σ)))) (MP (imply_contra₀ $ formalized_DNE σ) h₂);
    have h₄ : T ∪ {~σ} ⊢! ~Pr[T] ⸢~σ ⟶ ⊥⸣ ⟷ ~Pr[T ∪ {~σ}] ⸢⊥⸣ := by
      have : T₀ ⊢! ~Pr[T] ⸢~σ ⟶ ⊥⸣ ⟷ ~Pr[T ∪ {~σ}] ⸢⊥⸣ := FDT_neg _ _;
      exact weakening this;
    have h₅ := MP (iff_mp h₄) h₃;
    have h₆ : Inconsistent (T ∪ {~σ}) := Inconsistent_of_LConsistencyProvability _ h₅;
    simpa using consistent_or h₆;

variable
  [hSound : SigmaOneSound T]
  [Definable.Sigma (T ∪ {~~ConL[T]}) 1]
  [Derivability1 (T ∪ {~~ConL[T]}) (T ∪ {~~ConL[T]})]
  [Derivability2 (T ∪ {~~ConL[T]}) (T ∪ {~~ConL[T]})]
  [FormalizedCompleteness (T ∪ {~~ConL[T]}) (T ∪ {~~ConL[T]}) Σ 1]

theorem FormalizedUnprovabilityConsistency : T ⊬! (ConL[T]) ⟶ ~(Pr[T] ⸢(~ConL[T])⸣) := by
  by_contra H;
  have h₁ : T ⊢! Pr[T] ⸢~ConL[T]⸣ ⟶ ~ConL[T] := by have := imply_contra₃ H; nth_rw 2 [LConsistenncy]; simpa;
  have h₂ : T ⊢! ~ConL[T] := (LoebTheorem T₀ T (~ConL[T])).mpr h₁;
  exact (NotSigmaOneSoundness_of_LConsitencyRefutability T h₂).false hSound;

theorem FormalizedUnrefutabilityGoedelSentence (hG : IsGoedelSentence T G) (hGH : Hierarchy Π 1 G)
  : T ⊬! ConL[T] ⟶ ~Pr[T] ⸢~G⸣ := by
  by_contra H;
  have h₁ : T ⊢! ~G ⟷ ~ConL[T] := iff_contra $ equality_GoedelSentence_Consistency T hG hGH;
  have h₂ := iff_contra' $ MP (D2_iff T T) (D1 h₁);
  have h₃ := unprov_imp_right_iff (FormalizedUnprovabilityConsistency T₀ T) h₂;
  exact h₃ H;

end LO.FirstOrder.Arith.Incompleteness

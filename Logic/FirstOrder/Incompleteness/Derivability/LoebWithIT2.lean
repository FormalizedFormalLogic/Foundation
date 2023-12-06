import Logic.FirstOrder.Incompleteness.Derivability.Theory
import Logic.FirstOrder.Incompleteness.Derivability.Conditions
import Logic.FirstOrder.Incompleteness.Derivability.FirstIncompleteness
import Logic.FirstOrder.Incompleteness.Derivability.SecondIncompleteness

open LO.System LO.System.Intuitionistic

namespace LO.FirstOrder.Arith.Incompleteness

open FirstOrder.Theory HasProvablePred

variable (T₀ T : Theory ℒₒᵣ) [hSub : Subtheory T₀ T]
variable [Diagonizable T₀ Σ 1] [Diagonizable T₀ Π 1]
variable
  [HasProvablePred T]
  [HasProvablePred.Definable.Sigma T 1]
  [hD1 : Derivability1 T₀ T]
  [Derivability2 T₀ T]
  [Derivability3 T₀ T]
  [FormalizedDeductionTheorem T₀ T]

open Derivability1 Derivability2 FormalizedCompleteness FormalizedDeductionTheorem

variable (σ)
  [HasProvablePred (T ∪ {~σ})]
  [Definable.Sigma (T ∪ {~σ}) 1]

/-- Löb's Theorem *with* 2nd Incompleteness Theorem -/
theorem LoebTheorem : (T ⊢! σ) ↔ (T ⊢! ((Pr[T] ⸢σ⸣) ⟶ σ)) := by
  have : Subtheory T₀ (T ∪ {~σ}) := by sorry;
  have : Derivability1 T₀ (T ∪ {~σ}) := by sorry;
  have : Derivability2 T₀ (T ∪ {~σ}) := by sorry;
  have : Derivability3 T₀ (T ∪ {~σ}) := by sorry;

  apply Iff.intro;
  . intro H; simp only [hyp_right];
  . intro H;
    have h₁ : T ⊢! ~σ ⟶ ~Pr[T] ⸢σ⸣ := imp_contra₀ H;
    have h₂ : T ∪ {~σ} ⊢! ~Pr[T] ⸢σ⸣ := System.Deduction.deduction.mp h₁;
    have h₃ : T ∪ {~σ} ⊢! ~Pr[T] ⸢~σ ⟶ ⊥⸣ := (iff_mp (iff_contra (weakening $ @formalized_neg_def T _ (~σ)))) ⨀ ((imp_contra₀ $ formalized_DNE σ) ⨀ h₂);
    have h₄ : T ∪ {~σ} ⊢! ~Pr[T] ⸢~σ ⟶ ⊥⸣ ⟷ ~Pr[T ∪ {~σ}] ⸢⊥⸣ := by
      have : T₀ ⊢! ~Pr[T] ⸢~σ ⟶ ⊥⸣ ⟷ ~Pr[T ∪ {~σ}] ⸢⊥⸣ := FDT_neg _ _;
      exact weakening this;
    have h₅ := (iff_mp h₄) ⨀ h₃;
    have h₆ : Inconsistent (T ∪ {~σ}) := Inconsistent_of_LConsistencyProvability T₀ _ h₅;
    simpa using consistent_or h₆;

variable [hSound : SigmaOneSound T] [HasProvablePred (T ∪ {~~ConL[T]})] [Definable.Sigma (T ∪ {~~ConL[T]}) 1]

theorem FormalizedUnprovabilityConsistency : T ⊬! (ConL[T]) ⟶ ~(Pr[T] ⸢(~ConL[T])⸣) := by
  by_contra H;
  have h₁ : T ⊢! Pr[T] ⸢~ConL[T]⸣ ⟶ ~ConL[T] := by
    have := imp_contra₃ (by simpa using H);
    nth_rw 2 [LConsistenncy];
    simpa;
  have h₂ : T ⊢! ~ConL[T] := (LoebTheorem T₀ T (~ConL[T])).mpr h₁;
  exact (NotSigmaOneSoundness_of_LConsitencyRefutability T₀ T h₂).false hSound;

theorem FormalizedUnrefutabilityGoedelSentence (hG : IsGoedelSentence T₀ T G)
  : T ⊬! ConL[T] ⟶ ~Pr[T] ⸢~G⸣ := by
  by_contra H;
  suffices : T ⊬! ConL[T] ⟶ ~Pr[T] ⸢~G⸣; aesop;
  have h₁ : T ⊢! ~G ⟷ ~ConL[T] := iff_contra $ equality_GoedelSentence_Consistency T₀ T hG;
  have h₂ : T ⊢! ~Pr[T] ⸢~ConL[T]⸣ ⟷ ~Pr[T] ⸢~G⸣ := iff_contra' $ (weakening $ @D2_iff T₀ T _ _ _ _ _) ⨀ (hD1.D1' h₁);
  exact unprov_imp_right_iff (FormalizedUnprovabilityConsistency T₀ T) h₂;

end LO.FirstOrder.Arith.Incompleteness

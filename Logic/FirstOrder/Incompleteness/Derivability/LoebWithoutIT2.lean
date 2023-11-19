import Logic.FirstOrder.Incompleteness.Derivability.Theory
import Logic.FirstOrder.Incompleteness.Derivability.Conditions
import Logic.FirstOrder.Incompleteness.Derivability.FirstIncompleteness

namespace LO.FirstOrder.Arith.Incompleteness

open FirstOrder.Theory HasProvablePred FirstIncompleteness
open Derivability1 Derivability2 Derivability3

variable (T₀ T : Theory ℒₒᵣ) [SubTheory T₀ T]
variable [Diagonizable T Σ 1] [Diagonizable T Π 1]
variable
  [hConsis : Theory.Consistent T]
  [HasProvablePred T]
  [HasProvablePred.Definable.Sigma T 1]
  [Derivability1 T₀ T]
  [Derivability1 T T] -- TODO: remove this
  [Derivability2 T₀ T]
  [Derivability2 T T] -- TODO: remove this
  [Derivability3 T₀ T]
  [Derivability3 T T] -- TODO: remove this

/-- Löb's Theorem *without* 2nd Incompleteness Theorem -/
theorem LoebTheorem (σ : Sentence ℒₒᵣ) : T ⊢! σ ↔ T ⊢! (Pr[T] ⸢σ⸣ ⟶ σ) := by
  apply Iff.intro;
  . intro H; exact imply_intro_trivial H;
  . intro H;
    have ⟨K, hK⟩ := @existsKreiselSentence T _ 1 _ σ;
    have h₂ : T ⊢! Pr[T] ⸢K ⟶ (Pr[T] ⸢K⸣ ⟶ σ)⸣ := D1 (iff_mp $ weakening hK);
    have h₃ : T ⊢! Pr[T] ⸢K⸣ ⟶ Pr[T] ⸢Pr[T] ⸢K⸣ ⟶ σ⸣ := MP D2 h₂;
    have h₄ : T ⊢! Pr[T] ⸢Pr[T] ⸢K⸣ ⟶ σ⸣ ⟶ (Pr[T] ⸢Pr[T] ⸢K⸣⸣ ⟶ Pr[T] ⸢σ⸣) := D2;
    have h₅ : T ⊢! Pr[T] ⸢K⸣ ⟶ (Pr[T] ⸢Pr[T] ⸢K⸣⸣ ⟶ Pr[T] ⸢σ⸣) := imply_trans h₃ h₄;
    have h₆ : T ⊢! Pr[T] ⸢K⸣ ⟶ Pr[T] ⸢Pr[T] ⸢K⸣⸣ := D3;
    have h₇ : T ⊢! Pr[T] ⸢K⸣ ⟶ Pr[T] ⸢σ⸣ := imply_dilemma h₅ h₆;
    have h₈ : T ⊢! Pr[T] ⸢K⸣ ⟶ σ := imply_trans h₇ H;
    have h₉ : T ⊢! K := MP (iff_mpr $ weakening hK) h₈;
    exact MP h₈ (D1 h₉);

/-- 2nd Incompleteness Theorem via Löb's Theorem -/
theorem LConsistencyUnprovablility : T ⊬! (ConL[T]) := by
  by_contra hC;
  exact hConsis.consistent.false ((LoebTheorem T ⊥).mpr $ neg_imply_bot hC).some;

theorem HenkinSentenceProvability (hH : IsHenkinSentence T H) : T ⊢! H := (LoebTheorem T H).mpr (iff_mpr hH)

lemma existsProvableSentence : ∃ σ : Sentence ℒₒᵣ, T ⊢! σ := by
  have ⟨H, ⟨hH, _⟩⟩ := @existsHenkinSentence T _ 1 _ _;
  existsi H; exact HenkinSentenceProvability T hH

end LO.FirstOrder.Arith.Incompleteness

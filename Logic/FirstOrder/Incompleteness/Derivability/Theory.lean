import Logic.Logic.System
import Logic.Logic.HilbertStyle
import Logic.FirstOrder.Incompleteness.FirstIncompleteness

open LO.System

namespace LO.FirstOrder.Theory

open Subformula

variable {L : Language.{u}} [𝓑 : System (Sentence L)] (T : Theory L)

class Complete where
  complete : System.Complete T

abbrev Incomplete := IsEmpty (Theory.Complete T)

class Consistent where
  consistent : System.Consistent T

abbrev Inconsistent := IsEmpty (Theory.Consistent T)


section PropositionalCalculus

open System.Intuitionistic

variable {T : Theory L} [System.Intuitionistic (Sentence L)]

instance : BotDef (Sentence L) where
  bot_def := by simp;

instance : DoubleNeg (Sentence L) where
  double_neg := by simp;

instance : ImpDef (Sentence L) where
  imp_def := by simp [imp_eq];

instance : Subtheory T (T ∪ {σ}) where
  sub := by
    intro σ' h;
    exact weakening h (by simp)

@[simp]
lemma weakening [hs : Subtheory T₀ T] : (T₀ ⊢! σ) → (T ⊢! σ) := by
  simp;
  intro H;
  exact ⟨hs.sub H⟩;

lemma deduction {σ π} : (T ⊢! σ ⟶ π) ↔ (T ∪ {σ} ⊢! π) := by
  apply Iff.intro;
  . sorry;
  . sorry;

lemma consistent_or {T} {σ : Sentence L} : (Theory.Inconsistent (T ∪ {σ})) → (T ⊢! ~σ) := by sorry

@[simp]
lemma axm : T ∪ {σ} ⊢! σ := by sorry

lemma imply_intro {σ π} : (T ⊢! σ) → ((T ⊢! σ) → (T ⊢! π)) → (T ⊢! σ ⟶ π) := λ H₁ H₂ => hyp_right (H₂ H₁) _

lemma imply_dilemma : T ⊢! σ ⟶ (π ⟶ ρ) → T ⊢! (σ ⟶ π) → T ⊢! (σ ⟶ ρ) := by
  intro H₁ H₂;
  exact deduction.mpr $ (deduction.mp H₁) ⨀ (deduction.mp H₂);

lemma elim_and_left_dilemma : (T ⊢! (σ ⋏ π) ⟶ ρ) → (T ⊢! σ ⟶ π) → (T ⊢! σ ⟶ ρ) := by
  intro H₁ H₂;
  apply deduction.mpr;
  exact (weakening H₁) ⨀ (and_split axm $ deduction.mp H₂);

end PropositionalCalculus


end LO.FirstOrder.Theory

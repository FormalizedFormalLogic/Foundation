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

lemma or_intro : (T ⊢! σ ∨ T ⊢! π) → T ⊢! σ ⋎ π
  | .inl h => or_left h
  | .inr h => or_right h

lemma or_comm : T ⊢! σ ⋎ π → T ⊢! π ⋎ σ := or_symm

lemma and_intro : (T ⊢! σ) → (T ⊢! π) → (T ⊢! σ ⋏ π) := by
  intro H₁ H₂;
  exact ((conj₃ T σ π) ⨀ H₁) ⨀ H₂;

lemma imply_decomp : (T ⊢! σ ⟶ π) → (T ⊢! σ) → (T ⊢! π) := System.Intuitionistic.modus_ponens

alias MP := imply_decomp

lemma imply_intro_trivial {σ π} : (T ⊢! π) → (T ⊢! σ ⟶ π) := λ H => or_right H

lemma imply_intro {σ π} : (T ⊢! σ) → ((T ⊢! σ) → (T ⊢! π)) → (T ⊢! σ ⟶ π) := λ H₁ H₂ => imply_intro_trivial (H₂ H₁)

@[simp]
lemma imply_axm : T ⊢! σ ⟶ σ := deduction.mpr axm

lemma imply_contra₀ : (T ⊢! σ ⟶ π) → (T ⊢! ~π ⟶ ~σ) := by
  simp only [imp_eq, neg_neg']; intro H; exact or_comm H;

lemma imply_contra₁ : (T ⊢! σ ⟶ ~π) → (T ⊢! π ⟶ ~σ) := by
  intro H; simpa using (imply_contra₀ H);

lemma imply_contra₂ : (T ⊢! ~σ ⟶ π) → (T ⊢! ~π ⟶ σ) := by
  intro H; simpa using (imply_contra₀ H);

lemma imply_contra₃ : (T ⊢! ~σ ⟶ ~π) → (T ⊢! π ⟶ σ) := by
  intro H; simpa using (imply_contra₀ H);

lemma iff_comm : (T ⊢! σ ⟷ π) → (T ⊢! π ⟷ σ) := iff_symm

lemma iff_intro : (T ⊢! σ ⟶ π) → (T ⊢! π ⟶ σ) → (T ⊢! σ ⟷ π) := λ H₁ H₂ => and_intro H₁ H₂

lemma iff_contra : (T ⊢! σ ⟷ π) → (T ⊢! ~σ ⟷ ~π) := λ H => iff_intro (imply_contra₀ $ iff_mpr H) (imply_contra₀ $ iff_mp H)

lemma iff_contra' : (T ⊢! σ ⟷ π) → (T ⊢! ~π ⟷ ~σ) := λ H => iff_comm $ iff_contra H

lemma NC : (T ⊢! σ) → (T ⊢! ~σ) → (T ⊢! ⊥) := by
  intro H₁ H₂;
  have h₁ := imply₁ T σ ⊤ ⨀ H₁;
  have h₂ := imply₁ T (~σ) ⊤ ⨀ H₂;
  exact (neg₁ T ⊤ σ ⨀ h₁) ⨀ h₂;

lemma neg_imply_bot {σ} : (T ⊢! ~σ) → (T ⊢! σ ⟶ ⊥) := by
  intro H;
  simpa [neg_neg'] using (neg₂ T (~σ) ⊥ ⨀ H);

lemma neg_neg : (T ⊢! σ) ↔ (T ⊢! ~~σ) := by simp;

lemma EFQ : T ⊢! ⊥ ⟶ σ := efq T σ

lemma imply_dilemma : T ⊢! σ ⟶ (π ⟶ ρ) → T ⊢! (σ ⟶ π) → T ⊢! (σ ⟶ ρ) := by
  intro H₁ H₂;
  exact deduction.mpr $ MP (deduction.mp H₁) (deduction.mp H₂);

lemma elim_and_left_dilemma : (T ⊢! (σ ⋏ π) ⟶ ρ) → (T ⊢! σ ⟶ π) → (T ⊢! σ ⟶ ρ) := by
  intro H₁ H₂;
  apply deduction.mpr;
  exact MP (weakening H₁) (and_intro axm $ deduction.mp H₂);

end PropositionalCalculus


end LO.FirstOrder.Theory

import Logic.FirstOrder.Incompleteness.FirstIncompleteness


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

variable {T : Theory L} [hComplete : Complete T] [hConsistent : Consistent T]

@[simp]
lemma weakening [hs : SubTheory T₀ T] : (T₀ ⊢! σ) → (T ⊢! σ) := by simp; intro H; exact ⟨System.weakening H hs.sub⟩;

lemma deduction {σ π} : (T ⊢! σ ⟶ π) ↔ (T ∪ {σ} ⊢! π) := by
  apply Iff.intro;
  . sorry;
  . sorry;

lemma consistent_or {T} {σ : Sentence L} : (Theory.Inconsistent (T ∪ {σ})) → (T ⊢! ~σ) := by sorry

@[simp]
lemma axm : T ∪ {σ} ⊢! σ := by sorry

lemma or_intro_left : T ⊢! σ → T ⊢! σ ⋎ π := by sorry

lemma or_intro_right : T ⊢! π → T ⊢! σ ⋎ π := by sorry

lemma or_intro : (T ⊢! σ ∨ T ⊢! π) → T ⊢! σ ⋎ π
  | .inl h => or_intro_left h
  | .inr h => or_intro_right h

lemma or_comm : T ⊢! σ ⋎ π → T ⊢! π ⋎ σ := by sorry;

/-- TODO: おそらく`T`が`Complete`である必要がある -/
lemma or_decomp : T ⊢! σ ⋎ π → (T ⊢! σ ∨ T ⊢! π) := by sorry;

lemma or_elim_left : (T ⊢! σ ⋎ π) → (T ⊢! ~σ) → (T ⊢! π) := by
  intro H₁ H₂;
  by_contra C;
  cases or_decomp H₁ with
  | inl h => sorry; -- have a := hConsistent.consistent σ -- exact hCon.hbConsistent σ h H₂;
  | inr h => simp at C;

lemma or_elim_right : (T ⊢! σ ⋎ π) → (T ⊢! ~π) → (T ⊢! σ) := by
  intro H₁ H₂;
  exact or_elim_left (or_comm H₁) H₂;

lemma and_intro : (T ⊢! σ) → (T ⊢! π) → (T ⊢! σ ⋏ π) := by sorry

lemma and_comm : (T ⊢! σ ⋏ π) → (T ⊢! π ⋏ σ) := by
  simp;
  intro H;
  sorry

lemma and_left : (T ⊢! σ ⋏ π) → (T ⊢! σ) := by
  simp;
  intro H;
  sorry

lemma and_right : (T ⊢! σ ⋏ π) → (T ⊢! π) := λ H => and_left $ and_comm H


lemma imply_decomp : (T ⊢! σ ⟶ π) → (T ⊢! σ) → (T ⊢! π) := by
  intro H₁ H₂;
  simp only [imp_eq] at H₁;
  exact or_elim_left H₁ (by simpa [neg_neg']);

alias MP := imply_decomp

lemma imply_intro_trivial {σ π} : (T ⊢! π) → (T ⊢! σ ⟶ π) := λ H => or_intro_right H

lemma imply_intro {σ π} : (T ⊢! σ) → ((T ⊢! σ) → (T ⊢! π)) → (T ⊢! σ ⟶ π) := λ H₁ H₂ => imply_intro_trivial (H₂ H₁)

@[simp]
lemma imply_axm : T ⊢! σ ⟶ σ := deduction.mpr axm

lemma imply_trans : (T ⊢! σ ⟶ π) → (T ⊢! π ⟶ ρ) → (T ⊢! σ ⟶ ρ) := by
  intro H₁ H₂;
  apply deduction.mpr;
  exact MP (weakening H₂) (deduction.mp H₁);

lemma imply_contra₀ : (T ⊢! σ ⟶ π) → (T ⊢! ~π ⟶ ~σ) := by
  simp only [imp_eq, neg_neg']; intro H; exact or_comm H;

lemma imply_contra₁ : (T ⊢! σ ⟶ ~π) → (T ⊢! π ⟶ ~σ) := by
  intro H; simpa using (imply_contra₀ H);

lemma imply_contra₂ : (T ⊢! ~σ ⟶ π) → (T ⊢! ~π ⟶ σ) := by
  intro H; simpa using (imply_contra₀ H);

lemma imply_contra₃ : (T ⊢! ~σ ⟶ ~π) → (T ⊢! π ⟶ σ) := by
  intro H; simpa using (imply_contra₀ H);


lemma iff_comm : (T ⊢! σ ⟷ π) → (T ⊢! π ⟷ σ) := λ H => and_intro (and_right H) (and_left H)

lemma iff_mp : (T ⊢! σ ⟷ π) → (T ⊢! σ ⟶ π) := λ H => and_left H

lemma iff_mpr : (T ⊢! σ ⟷ π) → (T ⊢! π ⟶ σ) := λ h => iff_mp $ iff_comm h

lemma iff_intro : (T ⊢! σ ⟶ π) → (T ⊢! π ⟶ σ) → (T ⊢! σ ⟷ π) := λ H₁ H₂ => and_intro H₁ H₂

lemma iff_contra : (T ⊢! σ ⟷ π) → (T ⊢! ~σ ⟷ ~π) := λ H => iff_intro (imply_contra₀ $ iff_mpr H) (imply_contra₀ $ iff_mp H)

lemma iff_contra' : (T ⊢! σ ⟷ π) → (T ⊢! ~π ⟷ ~σ) := λ H => iff_comm $ iff_contra H

lemma iff_trans : (T ⊢! σ ⟷ π) → (T ⊢! π ⟷ ρ) → (T ⊢! σ ⟷ ρ) := by
  intro H₁ H₂;
  exact iff_intro (imply_trans (iff_mp H₁) (iff_mp H₂)) (imply_trans (iff_mpr H₂) (iff_mpr H₁));

lemma iff_unprov : (T ⊢! σ ⟷ π) → (T ⊬! σ) → (T ⊬! π) := by
  intro H Hn;
  by_contra HC;
  exact Hn $ MP (iff_mpr H) HC;

lemma unprov_imp_left_iff : (T ⊬! σ ⟶ π) → (T ⊢! σ ⟷ ρ) → (T ⊬! ρ ⟶ π) := by
  intro H₁ H₂;
  by_contra HC;
  exact H₁ $ imply_trans (iff_mp H₂) HC;

lemma unprov_imp_right_iff : (T ⊬! σ ⟶ π) → (T ⊢! π ⟷ ρ) → (T ⊬! σ ⟶ ρ) := by
  intro H₁ H₂;
  by_contra HC;
  exact H₁ $ imply_trans HC $ iff_mpr H₂;

lemma NC : (T ⊢! σ) → (T ⊢! ~σ) → (T ⊢! ⊥) := by
  intro H₁ H₂; sorry;

lemma neg_imply_bot {σ} : (T ⊢! ~σ) → (T ⊢! σ ⟶ ⊥) := by sorry;

lemma neg_neg : (T ⊢! σ) ↔ (T ⊢! ~~σ) := by simp;

lemma EFQ : T ⊢! ⊥ ⟶ σ := by sorry

lemma imply_dilemma : T ⊢! σ ⟶ (π ⟶ ρ) → T ⊢! (σ ⟶ π) → T ⊢! (σ ⟶ ρ) := by
  intro H₁ H₂;
  exact deduction.mpr $ MP (deduction.mp H₁) (deduction.mp H₂);

lemma elim_and_left_dilemma : (T ⊢! (σ ⋏ π) ⟶ ρ) → (T ⊢! σ ⟶ π) → (T ⊢! σ ⟶ ρ) := by
  intro H₁ H₂;
  apply deduction.mpr;
  exact MP (weakening H₁) (and_intro axm $ deduction.mp H₂);

end PropositionalCalculus


end LO.FirstOrder.Theory

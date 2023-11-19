import Logic.FirstOrder.Incompleteness.Derivability.Theory
import Logic.FirstOrder.Incompleteness.Derivability.Conditions

namespace LO.FirstOrder.Arith.Incompleteness

open FirstOrder.Theory HasProvablePred

variable (T₀ T : Theory ℒₒᵣ) [SubTheory T₀ T]
variable [Diagonizable T Π 1]
variable
  [Theory.Consistent T]
  [hPred : HasProvablePred T]
  [hPredDef : HasProvablePred.Definable.Sigma T 1]
  [HasProvablePred.Derivability1 T₀ T]
  [HasProvablePred.Derivability1 T T] -- TODO: remove this

variable (hG : IsGoedelSentence T G)

open HasProvablePred.Derivability1

lemma GoedelSentenceUnprovablility [hConsis : Theory.Consistent T] : T ⊬! G := by
  by_contra hP;
  have h₁ : T ⊢! (Pr[T] ⸢G⸣) := D1 hP;
  have h₂ : T ⊢! (Pr[T] ⸢G⸣) ⟶ ~G := by simpa using iff_mpr $ iff_contra hG;
  have hR : T ⊢! ~G := weakening (MP h₂ h₁);
  exact hConsis.consistent.false (NC hP hR).some;

lemma GoedelSentenceUnrefutability [hSound : SigmaOneSound T] : T ⊬! ~G := by
  by_contra hR;
  have h₁ : T ⊢! ~G ⟶ Pr[T] ⸢G⸣ := by have := iff_mp $ iff_contra hG; simpa [Subformula.neg_neg'] using this;
  have h₂ : T ⊢! Pr[T] ⸢G⸣ := MP h₁ hR; simp at h₂;
  have h₃ : ℕ ⊧ (Pr[T] ⸢G⸣) := hSound.sound (Hierarchy.rew _ hPredDef.definable) h₂;
  have hP : T ⊢! G := hPred.spec.mp h₃;
  exact (Consistent_of_SigmaOneSound T).consistent.false (NC hP hR).some;

theorem FirstIncompleteness [hSound : SigmaOneSound T] : Theory.Incomplete T := by
  have ⟨G, ⟨hG, _⟩⟩ := @existsGoedelSentence T _ 1 _ _;
  by_contra hCC; simp at hCC;
  cases (hCC.some.complete G) with
  | inl h => exact (GoedelSentenceUnprovablility T hG) h;
  | inr h => exact (GoedelSentenceUnrefutability T hG) h;

end LO.FirstOrder.Arith.Incompleteness

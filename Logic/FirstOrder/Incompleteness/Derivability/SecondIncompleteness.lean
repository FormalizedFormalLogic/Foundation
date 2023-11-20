import Logic.FirstOrder.Incompleteness.Derivability.Theory
import Logic.FirstOrder.Incompleteness.Derivability.Conditions
import Logic.FirstOrder.Incompleteness.Derivability.FirstIncompleteness

namespace LO.FirstOrder.Arith.Incompleteness

open FirstOrder.Theory HasProvablePred FirstIncompleteness

variable (T₀ T : Theory ℒₒᵣ) [SubTheory T₀ T]
variable [Diagonizable T₀ Π 1]
variable
  [HasProvablePred T]
  [HasProvablePred.Definable.Sigma T 1]
  [Derivability1 T₀ T]
  [Derivability2 T₀ T]
  [hFC : FormalizedCompleteness T₀ T Σ 1]

open Derivability1 Derivability2 FormalizedCompleteness

lemma FormalizedConsistency (σ : Sentence ℒₒᵣ) : T₀ ⊢! ~(Pr[T] ⸢σ⸣) ⟶ ConL[T] := by
  exact imply_contra₀ $ MP D2 $ D1 EFQ

variable (U : Theory ℒₒᵣ) [SubTheory T₀ U] in
private lemma extend {σ : Sentence ℒₒᵣ}
  : (U ⊢! ConL[T] ⟶ ~(Pr[T] ⸢σ⸣)) ↔ (U ⊢! (Pr[T] ⸢σ⸣) ⟶ (Pr[T] ⸢~σ⸣)) := by
  apply Iff.intro;
  . intro H;
    exact imply_contra₃ $ imply_trans (weakening $ FormalizedConsistency T₀ T (~σ)) H;
  . intro H;
    exact imply_contra₀ $ elim_and_left_dilemma (by
      have : T₀ ⊢! (Pr[T] ⸢σ⸣ ⋏ Pr[T] ⸢~σ⸣) ⟶ (Pr[T] ⸢⊥⸣) := formalized_NC' σ;
      exact weakening this
    ) H;

lemma equality_GoedelSentence_Consistency (hG : IsGoedelSentence T₀ T G) (hGh : Hierarchy Π 1 G) : T ⊢! G ⟷ ConL[T] := by
  have hnGh : Hierarchy Σ 1 (~G) := Hierarchy.neg hGh;
  have h₁ : T ⊢! ~G ⟶ (Pr[T] ⸢~G⸣) := weakening $ hFC.FC hnGh;
  have h₂ : T ⊢! Pr[T] ⸢G⸣ ⟶ ~G := by simpa using weakening $ iff_mp (iff_contra' hG);
  have h₃ : T ⊢! Pr[T] ⸢G⸣ ⟶ Pr[T] ⸢~G⸣ := imply_trans h₂ h₁;
  have h₄ : T ⊢! ConL[T] ⟶ ~Pr[T] ⸢G⸣ := (extend T₀ _ _).mpr h₃;
  have h₅ : T ⊢! ~Pr[T] ⸢G⸣ ⟶ ConL[T] := weakening $ FormalizedConsistency T₀ T G;
  exact iff_trans (weakening hG) $ iff_intro h₅ h₄;

theorem LConsistencyUnprovablility [hConsis : Theory.Consistent T] : T ⊬! ConL[T] := by
  have ⟨G, ⟨hG, hGh⟩⟩ := @existsGoedelSentence T₀ T _ _ 1 _ _;
  exact iff_unprov (equality_GoedelSentence_Consistency T₀ T hG hGh) (GoedelSentenceUnprovablility T₀ T hG);

lemma Inconsistent_of_LConsistencyProvability : T ⊢! ConL[T] → (Theory.Inconsistent T) := by
  intro hP;
  by_contra hConsis; simp at hConsis; have := hConsis.some;
  exact (LConsistencyUnprovablility T₀ T) hP;

theorem LConsistencyUnrefutability [hSound : SigmaOneSound T] : T ⊬! ~ConL[T] := by
  have ⟨G, ⟨hG, hGh⟩⟩ := @existsGoedelSentence T₀ T _ _ 1 _ _;
  exact iff_unprov (iff_contra $ equality_GoedelSentence_Consistency T₀ T hG hGh) (GoedelSentenceUnrefutability T₀ T hG);

lemma NotSigmaOneSoundness_of_LConsitencyRefutability : T ⊢! ~ConL[T] → IsEmpty (SigmaOneSound T) := by
  intro H;
  by_contra C; simp at C; have := C.some;
  exact (LConsistencyUnrefutability T₀ T).elim H;

end LO.FirstOrder.Arith.Incompleteness

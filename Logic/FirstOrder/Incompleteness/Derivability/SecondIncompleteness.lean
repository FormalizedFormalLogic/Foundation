import Logic.FirstOrder.Incompleteness.Derivability.Theory
import Logic.FirstOrder.Incompleteness.Derivability.Conditions
import Logic.FirstOrder.Incompleteness.Derivability.FirstIncompleteness

open LO.System LO.System.Intuitionistic

namespace LO.FirstOrder.Arith.Incompleteness

open FirstOrder.Theory HasProvablePred FirstIncompleteness

variable (T₀ T : Theory ℒₒᵣ) [Subtheory T₀ T]
variable [Diagonizable T₀ Π 1]
variable
  [HasProvablePred T]
  [HasProvablePred.Definable.Sigma T 1]
  [Derivability1 T₀ T]
  [Derivability2 T₀ T]
  [hD3 : Derivability3 T₀ T]

open Derivability1 Derivability2 Derivability3

lemma FormalizedConsistency (σ : Sentence ℒₒᵣ) : T₀ ⊢! ~(Pr[T] ⸢σ⸣) ⟶ ConL[T] := by
  exact imply_contra₀ $ MP D2 $ D1 EFQ

variable (U : Theory ℒₒᵣ) [Subtheory T₀ U] in
private lemma extend {σ : Sentence ℒₒᵣ}
  : (U ⊢! ConL[T] ⟶ ~Pr[T] ⸢σ⸣) ↔ (U ⊢! (Pr[T] ⸢σ⸣) ⟶ (Pr[T] ⸢~σ⸣)) := by
  apply Iff.intro;
  . intro H;
    exact imply_contra₃ $ imp_trans (weakening $ FormalizedConsistency T₀ T (~σ)) H;
  . intro H;
    exact imply_contra₀ $ elim_and_left_dilemma (by
      have : T₀ ⊢! (Pr[T] ⸢σ⸣ ⋏ Pr[T] ⸢~σ⸣) ⟶ (Pr[T] ⸢⊥⸣) := formalized_NC' σ;
      exact weakening this
    ) H;

variable (hG : IsGoedelSentence T₀ T G) (hGh : Hierarchy Π 1 G)

lemma formalizedGoedelSentenceUnprovablility : T ⊢! ConL[T] ⟶ ~Pr[T] ⸢G⸣ := by
  have h₁ : T ⊢! (Pr[T] ⸢G⸣) ⟶ (Pr[T] ⸢(Pr[T] ⸢G⸣)⸣) := hD3.D3';
  have h₂ : T ⊢! Pr[T] ⸢G⸣ ⟶ ~G := weakening $ imply_contra₁ $ iff_mp hG;
  have h₃ : T ⊢! Pr[T] ⸢Pr[T] ⸢G⸣⸣ ⟶ Pr[T] ⸢~G⸣ := weakening $ @formalized_imp_intro T₀ T _ _ _ _ _ h₂;
  exact (extend T₀ T T).mpr $ imp_trans h₁ h₃;

lemma equality_GoedelSentence_Consistency : T ⊢! G ⟷ ConL[T] := by
  have h₄ : T ⊢! ConL[T] ⟶ ~Pr[T] ⸢G⸣ := formalizedGoedelSentenceUnprovablility T₀ T hG;
  have h₅ : T ⊢! ~Pr[T] ⸢G⸣ ⟶ ConL[T] := weakening $ FormalizedConsistency T₀ T G;
  exact iff_trans (weakening hG) $ iff_intro h₅ h₄;

theorem LConsistencyUnprovablility [hConsis : Theory.Consistent T] : T ⊬! ConL[T] := by
  have ⟨G, ⟨hG, _⟩⟩ := @existsGoedelSentence T₀ T _ _ 1 _ _;
  exact iff_unprov (equality_GoedelSentence_Consistency T₀ T hG) (GoedelSentenceUnprovablility T₀ T hG);

lemma Inconsistent_of_LConsistencyProvability : T ⊢! ConL[T] → (Theory.Inconsistent T) := by
  intro hP;
  by_contra hConsis; simp at hConsis; have := hConsis.some;
  suffices : T ⊬! ConL[T]; aesop;
  exact LConsistencyUnprovablility T₀ T;

theorem LConsistencyUnrefutability [hSound : SigmaOneSound T] : T ⊬! ~ConL[T] := by
  have ⟨G, ⟨hG, _⟩⟩ := @existsGoedelSentence T₀ T _ _ 1 _ _;
  exact iff_unprov (iff_contra $ equality_GoedelSentence_Consistency T₀ T hG) (GoedelSentenceUnrefutability T₀ T hG);

lemma NotSigmaOneSoundness_of_LConsitencyRefutability : T ⊢! ~ConL[T] → IsEmpty (SigmaOneSound T) := by
  intro H;
  by_contra C; simp at C; have := C.some;
  suffices : T ⊬! ~ConL[T]; aesop;
  exact LConsistencyUnrefutability T₀ T;

end LO.FirstOrder.Arith.Incompleteness

import Logic.FirstOrder.Incompleteness.Derivability.Theory
import Logic.FirstOrder.Incompleteness.Derivability.Conditions
import Logic.FirstOrder.Incompleteness.Derivability.FirstIncompleteness

open LO.System LO.System.Intuitionistic

namespace LO.FirstOrder.Incompleteness

open FirstOrder.Theory HasProvablePred

variable {L : Language} [System (Sentence L)] [Intuitionistic (Sentence L)] [Deduction (Sentence L)] [GoedelNumber L (Sentence L)]
variable (T₀ T : Theory L) [Subtheory T₀ T]
variable {hDef} [Diagonizable T₀ hDef]
variable {M} [Structure L M]
variable [HasProvablePred T M] [hD1 : Derivability1 T₀ T M] [hD2 : Derivability2 T₀ T M] [hD3 : Derivability3 T₀ T M]

local notation:max "⸢" σ "⸣" => @GoedelNumber.encode L _ _ (σ : Sentence L)

open Derivability1 Derivability2 Derivability3

lemma FormalizedConsistency (σ : Sentence L) : T₀ ⊢! ~((Pr T M)/[⸢σ⸣]) ⟶ Con[T, M] := by
  exact imp_contra₀ $ D2 ⨀ D1 (efq _)

variable (U : Theory L) [Subtheory T₀ U] in
private lemma extend {σ : Sentence L}
  : (U ⊢! Con[T, M] ⟶ ~(Pr T M)/[⸢σ⸣]) ↔ (U ⊢! ((Pr T M)/[⸢σ⸣]) ⟶ ((Pr T M)/[⸢~σ⸣])) := by
  apply Iff.intro;
  . intro H;
    exact imp_contra₃ $ imp_trans (weakening $ FormalizedConsistency T₀ T (~σ)) H;
  . intro H;
    exact imp_contra₀ $ elim_and_left_dilemma (by
      have : T₀ ⊢! ((Pr T M)/[⸢σ⸣] ⋏ (Pr T M)/[⸢~σ⸣]) ⟶ ((Pr T M)/[⸢⊥⸣]) := formalized_NC' σ;
      exact weakening this
    ) H;

lemma formalizedGoedelSentenceUnprovablility (hG : IsGoedelSentence T₀ T M G) : T ⊢! Con[T, M] ⟶ ~(Pr T M)/[⸢G⸣] := by
  have h₁ : T ⊢! ((Pr T M)/[⸢G⸣]) ⟶ ((Pr T M)/[⸢((Pr T M)/[⸢G⸣])⸣]) := hD3.D3';
  simp [IsGoedelSentence] at hG;
  have h₂ : T ⊢! (Pr T M)/[⸢G⸣] ⟶ ~G := weakening $ imp_contra₁ $ iff_mp hG;
  have h₃ : T ⊢! (Pr T M)/[⸢(Pr T M)/[⸢G⸣]⸣] ⟶ (Pr T M)/[⸢~G⸣] := sorry; -- weakening $ @formalized_imp_intro _ _ _ _ _ T₀ T _ _ _ _ _ h₂;
  exact (extend T₀ T T).mpr $ imp_trans h₁ h₃;

lemma equality_GoedelSentence_Consistency (hG : IsGoedelSentence T₀ T M G) : T ⊢! G ⟷ Con[T, M] := by
  have h₄ : T ⊢! Con[T, M] ⟶ ~(Pr T M)/[⸢G⸣] := formalizedGoedelSentenceUnprovablility T₀ T hG;
  have h₅ : T ⊢! ~(Pr T M)/[⸢G⸣] ⟶ Con[T, M] := weakening $ FormalizedConsistency T₀ T G;
  exact iff_trans (weakening hG) $ iff_intro h₅ h₄;

variable [hConsis : Theory.Consistent T] [hSoundness : PrSoundness T M (λ σ => hDef σ)]
variable (a : hDef (~Pr T M))

theorem unprovable_consistency : T ⊬! Con[T, M] := by
  have ⟨G, ⟨hG, _⟩⟩ := existsGoedelSentence T₀ T M hDef a;
  exact iff_unprov (equality_GoedelSentence_Consistency T₀ T hG) (GoedelSentenceUnprovablility T₀ T M hG);

lemma Inconsistent_of_LConsistencyProvability : T ⊢! Con[T, M] → (Theory.Inconsistent T) := by
  intro hP;
  suffices : T ⊬! Con[T, M]; aesop;
  exact unprovable_consistency T₀ T a;

theorem unrefutable_consistency : T ⊬! (Pr T M)/[⸢⊥⸣] := by
  have ⟨G, ⟨hG, hGP⟩⟩ := existsGoedelSentence T₀ T M hDef a;
  simpa using iff_unprov (iff_contra $ equality_GoedelSentence_Consistency T₀ T hG) (GoedelSentenceUnrefutability T₀ T M hG hGP);

lemma NotSigmaOneSoundness_of_LConsitencyRefutability : T ⊢! ~Con[T, M] → IsEmpty (PrSoundness T M (λ σ => hDef σ)) := by
  intro H;
  suffices : T ⊬! ~Con[T, M]; aesop;
  simpa using unrefutable_consistency T₀ T a;

end LO.FirstOrder.Incompleteness

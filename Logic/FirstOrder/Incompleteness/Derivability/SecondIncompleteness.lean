import Logic.AutoProver.Prover
import Logic.FirstOrder.Incompleteness.Derivability.Theory
import Logic.FirstOrder.Incompleteness.Derivability.Conditions
import Logic.FirstOrder.Incompleteness.Derivability.FirstIncompleteness

open LO.System

namespace LO.FirstOrder.Incompleteness

open FirstOrder.Theory HasProvablePred

variable {L : Language} [GoedelNumber L (Sentence L)]
variable (T₀ T : Theory L) [Subtheory T₀ T]
variable {hDef} [Diagonizable T₀ hDef]
variable (M) [Structure L M]
variable [HasProvablePred T M] [hD1 : Derivability1 T₀ T M] [hD2 : Derivability2 T₀ T M] [hD3 : Derivability3 T₀ T M]

local notation:max "⸢" σ "⸣" => @GoedelNumber.encode L _ _ (σ : Sentence L)

open Derivability1 Derivability2 Derivability3

section

-- TODO: 削除したい

variable {T : Theory L}
lemma imp_contra₀ (h : T ⊢! p ⟶ q) : (T ⊢! ~q ⟶ ~p) := by prover [h];
lemma iff_unprov (h₁ : T ⊢! p ⟷ q) (h₂ : T ⊬! p) : T ⊬! q := by
  by_contra hC;
  suffices : T ⊢! p; aesop;
  have : T ⊢! q := by simpa using hC;
  exact by prover [h₁, this];

end

lemma formalizedImp (h : T ⊢! σ ⟶ π) : (T₀ ⊢! (Pr T M)/[⸢σ⸣] ⟶ (Pr T M)/[⸢π⸣]) := by prover [hD2.D2, (hD1.D1 h)];

lemma formalizedConsistency (σ : Sentence L) : T₀ ⊢! ~((Pr T M)/[⸢σ⸣]) ⟶ Con[T, M] := by
  have h₁ : T ⊢! ⊥ ⟶ σ := by tautology;
  exact imp_contra₀ (formalizedImp _ _ _ h₁);

variable (U : Theory L) [Subtheory T₀ U] in
private lemma extend {σ : Sentence L}
  : (U ⊢! Con[T, M] ⟶ ~(Pr T M)/[⸢σ⸣]) ↔ (U ⊢! ((Pr T M)/[⸢σ⸣]) ⟶ ((Pr T M)/[⸢~σ⸣])) := by
  apply Iff.intro;
  . intro H;
    have : U ⊢! ~((Pr T M)/[⸢~σ⸣]) ⟶ Con[T, M] := Theory.weakening $ formalizedConsistency T₀ T M (~σ);
    exact by prover [H, this];
  . intro H;
    have : T₀ ⊢! ((Pr T M)/[⸢σ⸣] ⋏ (Pr T M)/[⸢~σ⸣]) ⟶ ((Pr T M)/[⸢⊥⸣]) := formalized_NC' σ;
    have : U ⊢! ((Pr T M)/[⸢σ⸣] ⋏ (Pr T M)/[⸢~σ⸣]) ⟶ ((Pr T M)/[⸢⊥⸣]) := Theory.weakening $ this;
    exact imp_contra₀ $ elim_and_left_dilemma this H;

variable {G} (hG : GoedelSentence T₀ T M G)

lemma formalizedGoedelSentenceUnprovablility : T ⊢! Con[T, M] ⟶ ~(Pr T M)/[⸢G⸣] := by
  simp [GoedelSentence] at hG;
  have h₁ : T ⊢! ((Pr T M)/[⸢G⸣]) ⟶ ((Pr T M)/[⸢((Pr T M)/[⸢G⸣])⸣]) := hD3.D3';
  have h₂ : T₀ ⊢! (Pr T M)/[⸢G⸣] ⟶ ~G := by prover [hG];
  have h₂ : T ⊢! (Pr T M)/[⸢G⸣] ⟶ ~G := Theory.weakening h₂;
  have h₃ : T₀ ⊢! (Pr T M)/[⸢(Pr T M)/[⸢G⸣]⸣] ⟶ (Pr T M)/[⸢~G⸣] := formalizedImp _ _ _ h₂;
  have h₄ : T ⊢! (Pr T M)/[⸢(Pr T M)/[⸢G⸣]⸣] ⟶ (Pr T M)/[⸢~G⸣] := Theory.weakening h₃;
  have h₅ : T ⊢! (Pr T M)/[⸢G⸣] ⟶ (Pr T M)/[⸢~G⸣] := by prover [h₁, h₄];
  exact (extend T₀ T M T).mpr $ h₅;

lemma equality_GoedelSentence_Consistency : T ⊢! G ⟷ Con[T, M] := by
  simp [GoedelSentence] at hG;
  have h₁ : T ⊢! Con[T, M] ⟶ ~(Pr T M)/[⸢G⸣] := formalizedGoedelSentenceUnprovablility T₀ T M hG;
  have h₂ : T ⊢! ~(Pr T M)/[⸢G⸣] ⟶ Con[T, M] := Theory.weakening $ formalizedConsistency T₀ T M G;
  have : T ⊢! G ⟷ ~(Pr T M)/[⸢G⸣] := weakening hG;
  exact by prover [this, h₁, h₂];

variable [hConsis : Theory.Consistent T] [hSoundness : PrSoundness T M (λ σ => hDef σ)]
variable (a : hDef (~Pr T M))

theorem unprovable_consistency : T ⊬! Con[T, M] := by
  have ⟨G, ⟨hG, _⟩⟩ := existsGoedelSentence T₀ T M hDef a;
  exact iff_unprov (equality_GoedelSentence_Consistency T₀ T M hG) (GoedelSentenceUnprovablility T₀ T M hG);

lemma Inconsistent_of_LConsistencyProvability (hP : T ⊢! Con[T, M]) : (Theory.Inconsistent T) := by
  suffices : T ⊬! Con[T, M]; aesop;
  exact unprovable_consistency T₀ T M a;

theorem unrefutable_consistency : T ⊬! (Pr T M)/[⸢⊥⸣] := by
  have ⟨G, ⟨hG, hGP⟩⟩ := existsGoedelSentence T₀ T M hDef a;
  have h₁ : T ⊢! ~G ⟷ ~Con[T,M] := by prover [(equality_GoedelSentence_Consistency T₀ T M hG)];
  have h₂ := GoedelSentenceUnrefutability T₀ T M hG hGP;
  simpa using iff_unprov h₁ h₂;

lemma NotSigmaOneSoundness_of_LConsitencyRefutability : T ⊢! ~Con[T, M] → IsEmpty (PrSoundness T M (λ σ => hDef σ)) := by
  intro H;
  suffices : T ⊬! ~Con[T, M]; aesop;
  simpa using unrefutable_consistency T₀ T M a;

end LO.FirstOrder.Incompleteness

import Logic.AutoProver.Prover
import Logic.FirstOrder.Incompleteness.Derivability.Theory
import Logic.FirstOrder.Incompleteness.Derivability.Conditions

open LO.System

namespace LO.FirstOrder.Incompleteness

open FirstOrder.Theory HasProvablePred

variable {L : Language} [GoedelNumber L (Sentence L)]
variable (T₀ T : Theory L) [Subtheory T₀ T]
variable {hDef} [Diagonizable T₀ hDef]
variable (M) [Structure L M]
variable [hPred : HasProvablePred T M] [hD1 : Derivability1 T₀ T M]

local notation:max "⸢" σ "⸣" => @GoedelNumber.encode L _ _ (σ : Sentence L)

variable {G : Sentence L} (hG : GoedelSentence T₀ T M G)

variable [hConsis : Theory.Consistent T] [hSoundness : PrSoundness T M (λ σ => hDef σ)]

lemma GoedelSentenceUnprovablility : T ⊬! G := by
  by_contra hP; simp at hP; simp [GoedelSentence] at hG;
  have h₁ : T ⊢! (Pr T M)/[⸢G⸣] := hD1.D1' hP;
  have h₂ : T ⊢! (Pr T M)/[⸢G⸣] ⟶ ~G := weakening $ by prover [hG];
  have hR : T ⊢! ~G := by prover [h₁, h₂];
  exact broken_consistent hP hR;

lemma GoedelSentenceUnrefutability (a : hDef G) : T ⊬! ~G := by
  by_contra hR; simp at hR; simp [GoedelSentence] at hG;
  have h₁ : T ⊢! ~G ⟶ (Pr T M)/[⸢G⸣] := weakening $ by prover [hG];
  have h₂ : T ⊢! (Pr T M)/[⸢G⸣] := by prover [h₁, hR];
  have hP : T ⊢! G := hPred.spec.mp $ hSoundness.sounds a h₂;
  exact broken_consistent hP hR;

theorem FirstIncompleteness (a : hDef (~Pr T M)) : Theory.Incomplete T := by
  have γ := existsGoedelSentence T₀ T M hDef a;
  suffices ¬System.Complete T by exact ⟨this⟩;
  by_contra hC;
  cases (hC γ.choose) with
  | inl h => simpa using (GoedelSentenceUnprovablility T₀ T M γ.choose_spec.left);
  | inr h => simpa using (GoedelSentenceUnrefutability T₀ T M γ.choose_spec.left γ.choose_spec.right);

end LO.FirstOrder.Incompleteness

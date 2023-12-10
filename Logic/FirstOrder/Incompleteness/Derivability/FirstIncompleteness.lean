import Logic.Logic.HilbertStyle
import Logic.FirstOrder.Incompleteness.Derivability.Theory
import Logic.FirstOrder.Incompleteness.Derivability.Conditions

open LO.System LO.System.Intuitionistic

namespace LO.FirstOrder.Incompleteness

open FirstOrder.Theory HasProvablePred

variable {L : Language} [System (Sentence L)] [Intuitionistic (Sentence L)] [GoedelNumber L (Sentence L)]
variable (T₀ T : Theory L) [Subtheory T₀ T]
variable {P} [Diagonizable T₀ P]
variable (M) [Structure L M]
variable [hPred : HasProvablePred T M] [hD1 : Derivability1 T₀ T M]

local notation:max "⸢" σ "⸣" => @GoedelNumber.encode L _ _ (σ : Sentence L)

variable {G : Sentence L} (hG : IsGoedelSentence T₀ T M G)

variable [hConsis : Theory.Consistent T] [hSoundness : PrSoundness T M (λ _ => True)]

lemma GoedelSentenceUnprovablility : T ⊬! G := by
  by_contra hP; simp at hP;
  have h₁ : T ⊢! (Pr T M)/[⸢G⸣] := hD1.D1' hP;
  have h₂ : T ⊢! (Pr T M)/[⸢G⸣] ⟶ ~G := by simpa using weakening $ iff_mpr $ iff_contra hG;
  have hR : T ⊢! ~G := weakening (h₂ ⨀ h₁);
  exact broken_consistent hP hR;

lemma GoedelSentenceUnrefutability : T ⊬! ~G := by
  by_contra hR; simp at hR;
  have h₁ : T ⊢! ~G ⟶ (Pr T M)/[⸢G⸣] := by simpa [Subformula.neg_neg'] using weakening $ iff_mp $ iff_contra hG;
  have h₂ : T ⊢! (Pr T M)/[⸢G⸣] := h₁ ⨀ hR; simp at h₂;
  have h₃ : M ⊧ ((Pr T M)/[⸢G⸣]) := hSoundness.sounds (by simp) h₂;
  have hP : T ⊢! G := hPred.spec.mp h₃;
  exact broken_consistent hP hR;

theorem FirstIncompleteness (a : P 1 (~Pr T M)) : Theory.Incomplete T := by
  have γ := existsGoedelSentence T₀ T M P a;
  suffices ¬System.Complete T by exact ⟨this⟩;
  by_contra hC;
  cases (hC γ.choose) with
  | inl h => simpa using (GoedelSentenceUnprovablility T₀ T M γ.choose_spec.left);
  | inr h => simpa using (GoedelSentenceUnrefutability T₀ T M γ.choose_spec.left);

end LO.FirstOrder.Incompleteness

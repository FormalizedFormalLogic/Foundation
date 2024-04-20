import Logic.Modal.Normal.Strength.Init
import Logic.Modal.Normal.Soundness
import Logic.Modal.Normal.Completeness

/-!
  # Semantical Logical Strength Analysis

  Prepation to analyze the logical strength semantically.
  In principle, it is possible to compare the logical strength syntactically; that is, by proving that one axioms can derive the other's axioms
  However, it is somewhat cumbersome, so it is to be proved by reducing comparison of the definability of frame classes.
-/

namespace LO.Modal.Normal

variable {α β} [Inhabited β]
variable {Λ₁ Λ₂ : AxiomSet β}

namespace LogicalStrong

lemma of_subset_frameClass
  (hComp₂ : KripkeCompleteness Λ₂ (𝔽(Λ₂) : FrameClass γ))
  (h : (𝔽(Λ₂) : FrameClass γ) ⊆ (𝔽(Λ₁) : FrameClass γ))
  : (Λ₁ ≤ᴸ Λ₂) := by
  intro p h₁;
  apply hComp₂;
  intro F hF₂;
  apply AxiomSet.sounds h₁;
  exact h hF₂;

lemma of_axiomset_definability
  (hComp₂ : KripkeCompleteness Λ₂ (𝔽(Λ₂) : FrameClass γ))
  (hDef₁ : AxiomSetDefinability γ β Λ₁ P₁)
  (hDef₂ : AxiomSetDefinability γ β Λ₂ P₂)
  (hFrame₂₁ : ∀ {F : Frame γ}, P₂ F → P₁ F)
  : (Λ₁ ≤ᴸ Λ₂) := by
  apply of_subset_frameClass hComp₂;
  intro F hF;
  apply AxiomSetDefinability.iff_subset_frameClass hDef₁ |>.mp;
  exact hFrame₂₁ $ AxiomSetDefinability.iff_subset_frameClass hDef₂ |>.mpr hF;

end LogicalStrong

namespace LogicalStrictStrong

end LogicalStrictStrong

namespace LogicalEquivalence

lemma of_frameclass
  (hComp₁ : KripkeCompleteness Λ₁ (𝔽(Λ₁) : FrameClass γ₁))
  (hComp₂ : KripkeCompleteness Λ₂ (𝔽(Λ₂) : FrameClass γ₂))
  (h₁ : (𝔽(Λ₁) : FrameClass γ₁) ⊆ 𝔽(Λ₂))
  (h₂ : (𝔽(Λ₂) : FrameClass γ₂) ⊆ 𝔽(Λ₁))
  : (Λ₁ =ᴸ Λ₂) := by
  constructor;
  . apply LogicalStrong.of_subset_frameClass hComp₂; simpa;
  . apply LogicalStrong.of_subset_frameClass hComp₁; simpa;

lemma of_axiomset_definability
  (hComp₁ : KripkeCompleteness Λ₁ (𝔽(Λ₁) : FrameClass γ₁))
  (hComp₂ : KripkeCompleteness Λ₂ (𝔽(Λ₂) : FrameClass γ₂))
  (hDef₁₁ : AxiomSetDefinability γ₁ β Λ₁ P₁₁)
  (hDef₁₂ : AxiomSetDefinability γ₂ β Λ₁ P₁₂)
  (hDef₂₁ : AxiomSetDefinability γ₁ β Λ₂ P₂₁)
  (hDef₂₂ : AxiomSetDefinability γ₂ β Λ₂ P₂₂)
  (hFrame₁₂ : ∀ {F}, P₁₁ F → P₂₁ F)
  (hFrame₂₁ : ∀ {F}, P₂₂ F → P₁₂ F)
  : (Λ₁ =ᴸ Λ₂) := by
  constructor;
  . apply LogicalStrong.of_axiomset_definability hComp₂ hDef₁₂ hDef₂₂;
    assumption;
  . apply LogicalStrong.of_axiomset_definability hComp₁ hDef₂₁ hDef₁₁;
    assumption;

end LogicalEquivalence

end LO.Modal.Normal

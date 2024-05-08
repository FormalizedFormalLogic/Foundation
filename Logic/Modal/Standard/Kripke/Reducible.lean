import Logic.Modal.Standard.Deduction
import Logic.Modal.Standard.Kripke.Semantics

namespace LO.Modal.Standard

namespace Kripke

variable {W α : Type*} [DecidableEq α]
variable {Λ₁ Λ₂ : AxiomSet α} {P₁ P₂ : Frame W α → Prop}
variable (𝔽Λ₁ : AxiomSetFrameClass W Λ₁) (𝔽Λ₂ : AxiomSetFrameClass W Λ₂)
variable [hSound₁ : Sound Λ₁ 𝔽Λ₁] [hSound₂ : Sound Λ₂ 𝔽Λ₂]
variable [hComp₁ : Complete Λ₁ 𝔽Λ₁] [hComp₂ : Complete Λ₂ 𝔽Λ₂]
variable (hDec₁ : AxiomSetDefinability W Λ₁ P₁) (hDec₂ : AxiomSetDefinability W Λ₂ P₂)

lemma reducible_of_subset_axiomSetFrameClass (hs : 𝔽Λ₂.frameclass ⊆ 𝔽Λ₁.frameclass) : Λ₁ ≤ₛ Λ₂ := by
  apply System.reducible_iff.mpr;
  intro p hp;
  apply hComp₂.complete;
  intro F hF;
  exact hSound₁.sound hp F (hs hF);

lemma reducible_of_definability (hs : ∀ {F : Frame W α}, P₂ F → P₁ F) : Λ₁ ≤ₛ Λ₂ := by
  apply reducible_of_subset_axiomSetFrameClass 𝔽Λ₁ 𝔽Λ₂;
  intro h hF;
  apply iff_definability_memAxiomSetFrameClass hDec₁ |>.mp;
  exact hs $ iff_definability_memAxiomSetFrameClass hDec₂ |>.mpr hF;

lemma equiv_of_eq_axiomSetFrameClass (heq : 𝔽Λ₁.frameclass = 𝔽Λ₂.frameclass) : Λ₁ =ₛ Λ₂ := by
  apply System.Equiv.antisymm_iff.mpr;
  constructor;
  . exact reducible_of_subset_axiomSetFrameClass 𝔽Λ₁ 𝔽Λ₂ heq.symm.subset;
  . exact reducible_of_subset_axiomSetFrameClass 𝔽Λ₂ 𝔽Λ₁ heq.subset;

lemma equiv_of_iff_definability (h : ∀ {F : Frame W α}, P₁ F ↔ P₂ F) : Λ₁ =ₛ Λ₂ := by
  apply System.Equiv.antisymm_iff.mpr;
  constructor;
  . apply reducible_of_definability 𝔽Λ₁ 𝔽Λ₂ hDec₁ hDec₂;
    intro F hF;
    exact h.mpr hF;
  . apply reducible_of_definability 𝔽Λ₂ 𝔽Λ₁ hDec₂ hDec₁;
    intro F hF;
    exact h.mp hF;

end LO.Modal.Standard.Kripke

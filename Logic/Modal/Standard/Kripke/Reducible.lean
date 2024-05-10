import Logic.Modal.Standard.Deduction
import Logic.Modal.Standard.Kripke.Semantics

namespace LO.Modal.Standard

namespace Kripke

variable {W α : Type*} [DecidableEq α]
variable {Λ₁ Λ₂ : AxiomSet α} {P₁ P₂ : Frame W α → Prop}
variable [hSound₁ : Sound Λ₁ 𝔽(Λ₁, W)] [hSound₂ : Sound Λ₂ 𝔽(Λ₂, W)]
variable [hComp₁ : Complete Λ₁ 𝔽(Λ₁, W)] [hComp₂ : Complete Λ₂ 𝔽(Λ₂, W)]
variable (hDec₁ : AxiomSetDefinability W Λ₁ P₁) (hDec₂ : AxiomSetDefinability W Λ₂ P₂)

lemma reducible_of_subset_axiomSetFrameClass (hs : 𝔽(Λ₂, W) ⊆ 𝔽(Λ₁, W)) : Λ₁ ≤ₛ Λ₂ := by
  apply System.reducible_iff.mpr;
  intro p hp;
  apply hComp₂.complete;
  intro F hF;
  exact hSound₁.sound hp F (hs hF);

lemma reducible_of_definability (hs : ∀ {F : Frame W α}, P₂ F → P₁ F) : Λ₁ ≤ₛ Λ₂ := by
  apply reducible_of_subset_axiomSetFrameClass (W := W);
  intro h hF;
  apply iff_definability_memAxiomSetFrameClass hDec₁ |>.mp;
  exact hs $ iff_definability_memAxiomSetFrameClass hDec₂ |>.mpr hF;

lemma equiv_of_eq_axiomSetFrameClass (heq : 𝔽(Λ₁, W) = 𝔽(Λ₂, W)) : Λ₁ =ₛ Λ₂ := by
  apply System.Equiv.antisymm_iff.mpr;
  constructor;
  . exact reducible_of_subset_axiomSetFrameClass heq.symm.subset;
  . exact reducible_of_subset_axiomSetFrameClass heq.subset;

lemma equiv_of_iff_definability (h : ∀ {F : Frame W α}, P₁ F ↔ P₂ F) : Λ₁ =ₛ Λ₂ := by
  apply System.Equiv.antisymm_iff.mpr;
  constructor;
  . apply reducible_of_definability hDec₁ hDec₂;
    intro F hF;
    exact h.mpr hF;
  . apply reducible_of_definability hDec₂ hDec₁;
    intro F hF;
    exact h.mp hF;

end LO.Modal.Standard.Kripke

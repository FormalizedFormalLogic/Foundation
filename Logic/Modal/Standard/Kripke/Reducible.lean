import Logic.Modal.Standard.Deduction
import Logic.Modal.Standard.Kripke.Semantics

namespace LO.Modal.Standard

namespace Kripke

variable
  {α : Type u} [DecidableEq α]
  {L₁ L₂ : DeductionParameter α} [L₁.HasNec] [L₂.HasNec]
  {P₁ P₂ : FrameProperty α}
  [sound₁ : Sound L₁ 𝔽(Ax(L₁))] [sound₂ : Sound L₂ 𝔽(Ax(L₂))]
  [complete₁ : Complete L₁ 𝔽(Ax(L₁))] [complete₂ : Complete L₂ 𝔽(Ax(L₂))]
  [definability₁ : Definability Ax(L₁) P₁] [definability₂ : Definability Ax(L₂) P₂]

lemma reducible_of_subset_axiomSetFrameClass (hs : ∀ {W}, [Inhabited W] → ∀ {F}, 𝔽(Ax(L₂)) W F → 𝔽(Ax(L₁)) W F) : L₁ ≤ₛ L₂ := by
  apply System.reducible_iff.mpr;
  intro p hp;
  apply complete₂.complete;
  intro W _ F hF;
  exact sound₁.sound hp W F $ hs hF;

lemma reducible_of_definability (hs : ∀ {W}, [Inhabited W] → ∀ {F : Frame W α}, P₂ F → P₁ F) : L₁ ≤ₛ L₂ := by
  apply reducible_of_subset_axiomSetFrameClass;
  intro W _ F hF;
  apply iff_definability_memAxiomSetFrameClass definability₁ |>.mpr;
  exact hs $ iff_definability_memAxiomSetFrameClass definability₂ |>.mp hF;

lemma equiv_of_eq_axiomSetFrameClass
  (hs₁ : ∀ {W}, [Inhabited W] → ∀ {F}, 𝔽(Ax(L₂)) W F → 𝔽(Ax(L₁)) W F)
  (hs₂ : ∀ {W}, [Inhabited W] → ∀ {F}, 𝔽(Ax(L₁)) W F → 𝔽(Ax(L₂)) W F)
  : L₁ =ₛ L₂ := by
  apply System.Equiv.antisymm_iff.mpr;
  constructor;
  . apply reducible_of_subset_axiomSetFrameClass hs₁;
  . apply reducible_of_subset_axiomSetFrameClass hs₂;

lemma equiv_of_iff_definability (h : ∀ {W}, [Inhabited W] → ∀ {F : Frame W α}, P₁ F ↔ P₂ F) : L₁ =ₛ L₂ := by
  apply System.Equiv.antisymm_iff.mpr;
  constructor;
  . apply reducible_of_definability (definability₁ := definability₁) (definability₂ := definability₂); intros; exact h.mpr (by assumption)
  . apply reducible_of_definability (definability₁ := definability₂) (definability₂ := definability₁); intros; exact h.mp (by assumption)

end LO.Modal.Standard.Kripke

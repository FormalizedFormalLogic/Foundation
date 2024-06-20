import Logic.Modal.Standard.Deduction
import Logic.Modal.Standard.Kripke.Semantics

namespace LO.Modal.Standard

open DeductionParameter Normal

namespace Kripke

variable
  {α : Type*} [DecidableEq α]
  {Ax₁ Ax₂ : AxiomSet α} {𝔽₁ 𝔽₂ : FrameClass α}
  [sound₁ : Sound (Normal Ax₁) 𝔽₁] [sound₂ : Sound (Normal Ax₂) 𝔽₂]
  [complete₁ : Complete (Normal Ax₁) 𝔽₁] [complete₂ : Complete (Normal Ax₂) 𝔽₂]
  (definability₁ : Ax₁.DefinesKripkeFrameClass 𝔽₁) (definability₂ : Ax₂.DefinesKripkeFrameClass 𝔽₂)

lemma reducible_of_subset_axiomSetFrameClass (h₂₁ : ∀ {F : Frame α}, F ∈ 𝔽₂ → F ∈ 𝔽₁) : Ax₁ᴺ ≤ₛ Ax₂ᴺ := by
  apply System.reducible_iff.mpr;
  intro p hp;
  apply complete₂.complete;
  intro F hF;
  exact sound₁.sound hp F $ h₂₁ hF;

/-
lemma reducible_of_definability (hs : ∀ {F}, P₂ F → P₁ F) : L₁ ≤ₛ L₂ := by
  apply reducible_of_subset_axiomSetFrameClass;
  intro F hF;
  apply iff_definability_memAxiomSetFrameClass definability₁ |>.mpr;
  exact hs $ iff_definability_memAxiomSetFrameClass definability₂ |>.mp hF;
-/

lemma equiv_of_eq_axiomSetFrameClass
  (h₂₁ : ∀ {F}, F ∈ 𝔽₂ → F ∈ 𝔽₁)
  (h₁₂ : ∀ {F}, F ∈ 𝔽₁ → F ∈ 𝔽₂)
  : Ax₁ᴺ =ₛ Ax₂ᴺ := by
  apply System.Equiv.antisymm_iff.mpr;
  constructor;
  . apply reducible_of_subset_axiomSetFrameClass h₂₁;
  . apply reducible_of_subset_axiomSetFrameClass h₁₂;

/-
lemma equiv_of_iff_definability (h : ∀ {F}, P₁ F ↔ P₂ F) : L₁ =ₛ L₂ := by
  apply System.Equiv.antisymm_iff.mpr;
  constructor;
  . apply reducible_of_definability definability₁ definability₂; intros; exact h.mpr (by assumption)
  . apply reducible_of_definability definability₂ definability₁; intros; exact h.mp (by assumption)
-/

end LO.Modal.Standard.Kripke

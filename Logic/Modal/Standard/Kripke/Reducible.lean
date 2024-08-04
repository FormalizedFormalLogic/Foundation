import Logic.Modal.Standard.Deduction
import Logic.Modal.Standard.Kripke.Semantics

namespace LO.Modal.Standard

open DeductionParameter Normal

namespace Kripke

open LO.Kripke
open Formula

variable {α : Type*} {Ax₁ Ax₂ : AxiomSet α} (𝔽₁ 𝔽₂ : FrameClass)
  [sound₁ : Sound 𝝂Ax₁ (𝔽₁#α)] [sound₂ : Sound 𝝂Ax₂ (𝔽₂#α)]
  [complete₁ : Complete 𝝂Ax₁ (𝔽₁#α)] [complete₂ : Complete 𝝂Ax₂ (𝔽₂#α)]

lemma reducible_of_subset_FrameClass (h𝔽 : 𝔽₂ ⊆ 𝔽₁) : 𝝂Ax₁ ≤ₛ 𝝂Ax₂ := by
  apply System.weakerThan_iff.mpr;
  intro p hp;
  apply complete₂.complete;
  intro F hF;
  exact sound₁.sound hp $ h𝔽 hF;

lemma equiv_of_eq_FrameClass (h𝔽 : 𝔽₁ = 𝔽₂) : 𝝂Ax₁ =ₛ 𝝂Ax₂ := by
  apply System.Equiv.antisymm_iff.mpr;
  constructor;
  . apply reducible_of_subset_FrameClass 𝔽₁ 𝔽₂; subst_vars; rfl;
  . apply reducible_of_subset_FrameClass 𝔽₂ 𝔽₁; subst_vars; rfl;

end LO.Modal.Standard.Kripke

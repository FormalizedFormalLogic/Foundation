import Logic.Modal.Standard.Deduction
import Logic.Modal.Standard.Kripke.Semantics

namespace LO.Modal.Standard

namespace Kripke

variable {W : Type*} {α : Type u} [DecidableEq α]
variable {Λ₁ Λ₂ : AxiomSet α} {P₁ P₂ : ∀ {W : Type u}, [Inhabited W] → Frame W α → Prop}
variable [hSound₁ : Sound Λ₁ 𝔽(Λ₁)] [hSound₂ : Sound Λ₂ 𝔽(Λ₂)]
variable [hComp₁ : Complete Λ₁ 𝔽(Λ₁)] [hComp₂ : Complete Λ₂ 𝔽(Λ₂)]
variable (hDef₁ : AxiomSetDefinability Λ₁ P₁) (hDef₂ : AxiomSetDefinability Λ₂ P₂)

lemma reducible_of_subset_axiomSetFrameClass (hs : ∀ {W}, [hiW : Inhabited W] → ∀ {F}, 𝔽(Λ₂) W hiW F → 𝔽(Λ₁) W hiW F) : Λ₁ ≤ₛ Λ₂ := by
  apply System.reducible_iff.mpr;
  intro p hp;
  apply hComp₂.complete;
  intro W _ F hF;
  exact hSound₁.sound hp W F $ hs hF;

lemma reducible_of_definability (hs : ∀ {W}, [Inhabited W] → ∀ {F : Frame W α}, P₂ F → P₁ F) : Λ₁ ≤ₛ Λ₂ := by
  apply reducible_of_subset_axiomSetFrameClass;
  intro W hiW F hF;
  apply iff_definability_memAxiomSetFrameClass hDef₁ |>.mpr;
  exact hs $ iff_definability_memAxiomSetFrameClass hDef₂ |>.mp hF;

lemma equiv_of_eq_axiomSetFrameClass
  (hs₁ : ∀ {W}, [hiW : Inhabited W] → ∀ {F}, 𝔽(Λ₂) W hiW F → 𝔽(Λ₁) W hiW F)
  (hs₂ : ∀ {W}, [hiW : Inhabited W] → ∀ {F}, 𝔽(Λ₁) W hiW F → 𝔽(Λ₂) W hiW F)
  : Λ₁ =ₛ Λ₂ := by
  apply System.Equiv.antisymm_iff.mpr;
  constructor;
  . apply reducible_of_subset_axiomSetFrameClass hs₁;
  . apply reducible_of_subset_axiomSetFrameClass hs₂;

lemma equiv_of_iff_definability (h : ∀ {W}, [Inhabited W] → ∀ {F : Frame W α}, P₁ F ↔ P₂ F) : Λ₁ =ₛ Λ₂ := by
  apply System.Equiv.antisymm_iff.mpr;
  constructor;
  . apply reducible_of_definability hDef₁ hDef₂;
    intros; apply h.mpr; assumption;
  . apply reducible_of_definability hDef₂ hDef₁;
    intros; apply h.mp; assumption;

end LO.Modal.Standard.Kripke

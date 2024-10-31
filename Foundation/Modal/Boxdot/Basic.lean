import Foundation.Modal.Hilbert

namespace LO.Modal

variable [DecidableEq α]

def Formula.BoxdotTranslation : Formula α → Formula α
  | atom φ => .atom φ
  | ⊥ => ⊥
  | φ ➝ ψ => (BoxdotTranslation φ) ➝ (BoxdotTranslation ψ)
  | □φ => ⊡(BoxdotTranslation φ)
postfix:90 "ᵇ" => Formula.BoxdotTranslation


class BoxdotProperty (Λ₁ Λ₂ : Hilbert α) where
  bdp {φ} : Λ₁ ⊢! φ ↔ Λ₂ ⊢! pᵇ


open System
open Formula

variable {φ : Formula α}

theorem boxdotTranslated
  {Λ₁ Λ₂ : Hilbert α} [Λ₁.IsNormal] [Λ₂.IsNormal]
  (h : ∀ φ ∈ Λ₁.axioms, Λ₂ ⊢! pᵇ) : Λ₁ ⊢! φ → Λ₂ ⊢! pᵇ := by
  intro d;
  induction d using Deduction.inducition_with_necOnly! with
  | hMaxm hs => exact h _ hs;
  | hNec ihp =>
    dsimp [BoxdotTranslation];
    exact boxdot_nec! $ ihp;
  | hMdp ihpq ihp =>
    dsimp only [BoxdotTranslation] at ihpq;
    exact ihpq ⨀ ihp;
  | _ =>
    dsimp only [BoxdotTranslation];
    trivial;

lemma boxdotTranslatedK4_of_S4 : 𝐒𝟒 ⊢! φ → 𝐊𝟒 ⊢! pᵇ := boxdotTranslated $ by
  intro φ hp;
  simp at hp;
  rcases hp with (⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩);
  . dsimp [BoxdotTranslation]; exact boxdot_axiomK!;
  . dsimp [BoxdotTranslation]; exact boxdot_axiomT!;
  . dsimp [BoxdotTranslation]; exact boxdot_axiomFour!

lemma iff_boxdotTranslation_S4 : 𝐒𝟒 ⊢! φ ⭤ pᵇ := by
  induction φ using Formula.rec' with
  | hbox φ ihp => exact iff_trans''! (box_iff! ihp) iff_box_boxdot!;
  | himp φ ψ ihp ihq => exact imp_replace_iff! ihp ihq;
  | _ => exact iff_id!;

lemma S4_of_boxdotTranslatedK4 (h : 𝐊𝟒 ⊢! pᵇ) : 𝐒𝟒 ⊢! φ := by
  exact (and₂'! iff_boxdotTranslation_S4) ⨀ (weakerThan_iff.mp $ K4_weakerThan_S4) h

theorem iff_S4_boxdotTranslatedK4 : 𝐒𝟒 ⊢! φ ↔ 𝐊𝟒 ⊢! pᵇ := by
  constructor;
  . apply boxdotTranslatedK4_of_S4;
  . apply S4_of_boxdotTranslatedK4;
instance : BoxdotProperty (𝐒𝟒 : Hilbert α) 𝐊𝟒 := ⟨iff_S4_boxdotTranslatedK4⟩

end LO.Modal

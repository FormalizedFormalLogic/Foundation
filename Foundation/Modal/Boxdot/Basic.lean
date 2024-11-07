import Foundation.Modal.Hilbert

namespace LO.Modal

variable [DecidableEq α]

def Formula.BoxdotTranslation : Formula α → Formula α
  | atom φ => .atom φ
  | ⊥ => ⊥
  | φ ➝ ψ => (BoxdotTranslation φ) ➝ (BoxdotTranslation ψ)
  | □φ => ⊡(BoxdotTranslation φ)
postfix:90 "ᵇ" => Formula.BoxdotTranslation


class BoxdotProperty (H₁ H₂ : Hilbert α) where
  bdp {φ} : H₁ ⊢! φ ↔ H₂ ⊢! φᵇ


open System
open Formula
open Hilbert.Deduction

variable {φ : Formula α}

theorem boxdotTranslated
  {H₁ H₂ : Hilbert α} [H₁.IsNormal] [H₂.IsNormal]
  (h : ∀ φ ∈ H₁.axioms, H₂ ⊢! φᵇ) : H₁ ⊢! φ → H₂ ⊢! φᵇ := by
  intro d;
  induction d using inducition_with_necOnly! with
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

lemma boxdotTranslatedK4_of_S4 : (Hilbert.S4 α) ⊢! φ → (Hilbert.K4 α) ⊢! φᵇ := boxdotTranslated $ by
  intro φ hp;
  simp at hp;
  rcases hp with (⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩);
  . dsimp [BoxdotTranslation]; exact boxdot_axiomK!;
  . dsimp [BoxdotTranslation]; exact boxdot_axiomT!;
  . dsimp [BoxdotTranslation]; exact boxdot_axiomFour!

lemma iff_boxdotTranslation_S4 : (Hilbert.S4 α) ⊢! φ ⭤ φᵇ := by
  induction φ using Formula.rec' with
  | hbox φ ihp => exact iff_trans''! (box_iff! ihp) iff_box_boxdot!;
  | himp φ ψ ihp ihq => exact imp_replace_iff! ihp ihq;
  | _ => exact iff_id!;

lemma S4_of_boxdotTranslatedK4 (h : (Hilbert.K4 α) ⊢! φᵇ) : (Hilbert.S4 α) ⊢! φ := by
  exact (and₂'! iff_boxdotTranslation_S4) ⨀ (weakerThan_iff.mp $ Hilbert.K4_weakerThan_S4) h

theorem iff_S4_boxdotTranslatedK4 : (Hilbert.S4 α) ⊢! φ ↔ (Hilbert.K4 α) ⊢! φᵇ := by
  constructor;
  . apply boxdotTranslatedK4_of_S4;
  . apply S4_of_boxdotTranslatedK4;
instance : BoxdotProperty (Hilbert.S4 α) (Hilbert.K4 α) := ⟨iff_S4_boxdotTranslatedK4⟩

end LO.Modal

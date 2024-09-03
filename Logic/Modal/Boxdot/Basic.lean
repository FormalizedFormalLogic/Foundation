import Logic.Modal.Deduction

namespace LO.Modal

variable [DecidableEq α]

def Formula.BoxdotTranslation : Formula α → Formula α
  | atom p => .atom p
  | ⊥ => ⊥
  | p ⟶ q => (BoxdotTranslation p) ⟶ (BoxdotTranslation q)
  | □p => ⊡(BoxdotTranslation p)
postfix:90 "ᵇ" => Formula.BoxdotTranslation


class BoxdotProperty (Λ₁ Λ₂ : DeductionParameter α) where
  bdp {p} : Λ₁ ⊢! p ↔ Λ₂ ⊢! pᵇ


open System
open Formula

variable {p : Formula α}

theorem boxdotTranslated
  {Λ₁ Λ₂ : DeductionParameter α} [Λ₁.IsNormal] [Λ₂.IsNormal]
  (h : ∀ p ∈ Ax(Λ₁), Λ₂ ⊢! pᵇ) : Λ₁ ⊢! p → Λ₂ ⊢! pᵇ := by
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

lemma boxdotTranslatedK4_of_S4 : 𝐒𝟒 ⊢! p → 𝐊𝟒 ⊢! pᵇ := boxdotTranslated $ by
  intro p hp;
  rcases hp with (⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩);
  . dsimp [BoxdotTranslation]; exact boxdot_axiomK!;
  . dsimp [BoxdotTranslation]; exact boxdot_axiomT!;
  . dsimp [BoxdotTranslation]; exact boxdot_axiomFour!

lemma iff_boxdotTranslation_S4 : 𝐒𝟒 ⊢! p ⟷ pᵇ := by
  induction p using Formula.rec' with
  | hbox p ihp => exact iff_trans''! (box_iff! ihp) iff_box_boxdot!;
  | himp p q ihp ihq => exact imp_replace_iff! ihp ihq;
  | _ => exact iff_id!;

lemma S4_of_boxdotTranslatedK4 (h : 𝐊𝟒 ⊢! pᵇ) : 𝐒𝟒 ⊢! p := by
  exact (and₂'! iff_boxdotTranslation_S4) ⨀ (weakerThan_iff.mp $ reducible_K4_S4) h

theorem iff_S4_boxdotTranslatedK4 : 𝐒𝟒 ⊢! p ↔ 𝐊𝟒 ⊢! pᵇ := by
  constructor;
  . apply boxdotTranslatedK4_of_S4;
  . apply S4_of_boxdotTranslatedK4;
instance : BoxdotProperty (𝐒𝟒 : DeductionParameter α) 𝐊𝟒 := ⟨iff_S4_boxdotTranslatedK4⟩

end LO.Modal

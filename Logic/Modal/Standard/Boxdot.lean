import Logic.Modal.Standard.Deduction

namespace LO.Modal.Standard

variable [DecidableEq α]

def Formula.BoxdotTranslation : Formula α → Formula α
  | atom p => .atom p
  | ⊥ => ⊥
  | p ⟶ q => (BoxdotTranslation p) ⟶ (BoxdotTranslation q)
  | □p => ⊡(BoxdotTranslation p)
postfix:75 "ᵇ" => Formula.BoxdotTranslation

open System
open Formula

variable {p : Formula α}

lemma boxdotTranslatedK4_of_S4 (h : 𝐒𝟒 ⊢! p) : 𝐊𝟒 ⊢! pᵇ := by
  induction h using Deduction.inducition_with_necOnly! with
  | hMaxm a =>
    rcases a with (hK | hT | hFour);
    . obtain ⟨_, _, e⟩ := hK; subst_vars; dsimp [Axioms.K, BoxdotTranslation]; apply boxdot_axiomK!;
    . obtain ⟨_, e⟩ := hT; subst_vars; dsimp [Axioms.T, BoxdotTranslation]; apply boxdot_axiomT!;
    . obtain ⟨_, e⟩ := hFour; subst_vars; dsimp [Axioms.Four, BoxdotTranslation]; apply boxdot_axiomFour!;
  | hNec ihp =>
    dsimp [BoxdotTranslation];
    exact boxdot_nec! $ ihp;
  | hMdp ihpq ihp =>
    dsimp [BoxdotTranslation] at ihpq ihp;
    exact ihpq ⨀ ihp;
  | _ => dsimp [BoxdotTranslation]; trivial;

lemma iff_boxdotTranslation_S4 : 𝐒𝟒 ⊢! p ⟷ pᵇ := by
  induction p using Formula.minimum_rec' with
  | himp p q ihp ihq => dsimp [BoxdotTranslation]; exact imp_replace_iff! ihp ihq;
  | hbox p ihp => dsimp [BoxdotTranslation]; exact iff_trans''! (box_iff! ihp) iff_box_boxdot!;
  | _ => dsimp [BoxdotTranslation]; exact iff_id!;

lemma S4_of_boxdotTranslatedK4 (h : 𝐊𝟒 ⊢! pᵇ) : 𝐒𝟒 ⊢! p := by
  exact (and₂'! iff_boxdotTranslation_S4) ⨀ (weakerThan_iff.mp $ reducible_K4_S4) h

theorem iff_S4_boxdotTranslatedK4 : 𝐒𝟒 ⊢! p ↔ 𝐊𝟒 ⊢! pᵇ := by
  constructor;
  . apply boxdotTranslatedK4_of_S4;
  . apply S4_of_boxdotTranslatedK4;

lemma boxdotTranslatedGL_of_Grz : 𝐆𝐫𝐳 ⊢! p → 𝐆𝐋 ⊢! pᵇ := by
  intro h;
  induction h using Deduction.inducition_with_necOnly! with
  | hMaxm a =>
    rcases a with (⟨_, _, rfl⟩ | ⟨_, rfl⟩);
    . exact boxdot_axiomK!;
    . exact boxdot_Grz_of_L!;
  | hNec ihp =>
    dsimp [BoxdotTranslation];
    exact boxdot_nec! $ ihp;
  | hMdp ihpq ihp =>
    dsimp [BoxdotTranslation] at ihpq ihp;
    exact ihpq ⨀ ihp;
  | _ => dsimp [BoxdotTranslation]; trivial;

end LO.Modal.Standard

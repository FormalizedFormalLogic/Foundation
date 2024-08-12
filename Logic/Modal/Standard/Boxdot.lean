import Logic.Modal.Standard.Deduction

namespace LO.Modal.Standard

variable [DecidableEq α]

def Formula.BoxdotTranslation : Formula α → Formula α
  | atom p => .atom p
  | ⊥ => ⊥
  | p ⟶ q => (BoxdotTranslation p) ⟶ (BoxdotTranslation q)
  | □p => ⊡(BoxdotTranslation p)
postfix:90 "ᵇ" => Formula.BoxdotTranslation

namespace Formula.BoxdotTranslation

variable {p q : Formula α}

lemma top_def : (⊤ : Formula α)ᵇ = ⊤ := by rfl;

lemma box_def : (□p)ᵇ = ⊡(pᵇ) := by rfl;

lemma imp_def : (p ⟶ q)ᵇ = (pᵇ ⟶ qᵇ) := by rfl;

lemma neg_def : (~p)ᵇ = ~(pᵇ) := by rfl;

lemma and_def : (p ⋏ q)ᵇ = (pᵇ ⋏ qᵇ) := by rfl;

lemma or_def : (p ⋎ q)ᵇ = (pᵇ ⋎ qᵇ) := by rfl;

lemma iff_def : (p ⟷ q)ᵇ = (pᵇ ⟷ qᵇ) := by rfl;

lemma axiomK : (Axioms.K p q)ᵇ = ⊡(pᵇ ⟶ qᵇ) ⟶ ⊡(pᵇ) ⟶ ⊡(qᵇ) := by rfl;

lemma axiomT : (Axioms.T p)ᵇ = ⊡(pᵇ) ⟶ pᵇ := by rfl;

lemma axiomFour : (Axioms.Four p)ᵇ = ⊡(pᵇ) ⟶ ⊡⊡(pᵇ) := by rfl;

lemma axiomL : (Axioms.L p)ᵇ = ⊡(⊡pᵇ ⟶ pᵇ) ⟶ ⊡pᵇ := by rfl;

lemma axiomGrz : (Axioms.Grz p)ᵇ =  ⊡(⊡(pᵇ ⟶ ⊡pᵇ) ⟶ pᵇ) ⟶ pᵇ := by rfl;

end Formula.BoxdotTranslation

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
    simp only [BoxdotTranslation.imp_def] at ihpq;
    exact ihpq ⨀ ihp;
  | _ =>
    simp only [BoxdotTranslation.imp_def, BoxdotTranslation.neg_def, BoxdotTranslation.top_def, BoxdotTranslation.iff_def];
    trivial;

lemma boxdotTranslatedK4_of_S4 : 𝐒𝟒 ⊢! p → 𝐊𝟒 ⊢! pᵇ := boxdotTranslated $ by
  intro p hp;
  rcases hp with (⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩);
  . simp only [BoxdotTranslation.axiomK, boxdot_axiomK!];
  . simp only [BoxdotTranslation.axiomT, boxdot_axiomT!];
  . simp only [BoxdotTranslation.axiomFour, boxdot_axiomFour!];

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

lemma boxdotTranslatedGL_of_Grz : 𝐆𝐫𝐳 ⊢! p → 𝐆𝐋 ⊢! pᵇ := boxdotTranslated $ by
  intro p hp;
  rcases hp with (⟨_, _, rfl⟩ | ⟨_, rfl⟩);
  . simp only [BoxdotTranslation.axiomK, boxdot_axiomK!];
  . simp only [BoxdotTranslation.axiomGrz, boxdot_Grz_of_L!];

end LO.Modal.Standard

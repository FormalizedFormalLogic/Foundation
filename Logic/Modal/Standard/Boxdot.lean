import Logic.Modal.Standard.Deduction

namespace LO.Modal.Standard

variable [DecidableEq α]

def Formula.BoxdotTranslation : Formula α → Formula α
  | atom p => .atom p
  | natom p => .natom p
  | ⊥ => ⊥
  | ⊤ => ⊤
  | p ⋏ q => (BoxdotTranslation p) ⋏ (BoxdotTranslation q)
  | p ⋎ q => (BoxdotTranslation p) ⋎ (BoxdotTranslation q)
  | □p => ⊡(BoxdotTranslation p)
  | ◇p => ⟐(BoxdotTranslation p)
postfix:90 "ᵇ" => Formula.BoxdotTranslation

namespace Formula.BoxdotTranslation

variable {p q : Formula α}

lemma top_def : (⊤ : Formula α)ᵇ = ⊤ := by rfl;

lemma box_def : (□p)ᵇ = ⊡(pᵇ) := by rfl;

lemma neg_def : (~p)ᵇ = ~(pᵇ) := by
  induction p using Formula.rec' <;> simp [BoxdotTranslation, Formula.neg_eq, *];

lemma and_def : (p ⋏ q)ᵇ = (pᵇ ⋏ qᵇ) := by
  induction p using Formula.rec' with
  | hand p q ihp ihq => simp [BoxdotTranslation, Formula.and_eq, ihp, ihq];
  | _ => simp [BoxdotTranslation, Formula.and_eq];

lemma or_def : (p ⋎ q)ᵇ = (pᵇ ⋎ qᵇ) := by
  induction p using Formula.rec' with
  | hor p q ihp ihq => simp [BoxdotTranslation, Formula.or_eq, ihp, ihq];
  | _ => simp [BoxdotTranslation, Formula.or_eq];

lemma imp_def : (p ⟶ q)ᵇ = (pᵇ ⟶ qᵇ) := by
  simp [BoxdotTranslation, Formula.imp_eq];
  rw [Formula.neg_eq];
  simp [neg_def];

lemma iff_def : (p ⟷ q)ᵇ = (pᵇ ⟷ qᵇ) := by simp only [Formula.iff_eq, and_def, imp_def];

lemma axiomK : (Axioms.K p q)ᵇ = ⊡(pᵇ ⟶ qᵇ) ⟶ ⊡(pᵇ) ⟶ ⊡(qᵇ) := by simp [Axioms.K, imp_def, box_def];

lemma axiomT : (Axioms.T p)ᵇ = ⊡(pᵇ) ⟶ pᵇ := by simp [Axioms.T, imp_def, box_def];

lemma axiomFour : (Axioms.Four p)ᵇ = ⊡(pᵇ) ⟶ ⊡⊡(pᵇ) := by simp [Axioms.Four, imp_def, box_def];

lemma axiomL : (Axioms.L p)ᵇ = ⊡(⊡pᵇ ⟶ pᵇ) ⟶ ⊡pᵇ := by simp [Axioms.L, imp_def, box_def];

lemma axiomGrz : (Axioms.Grz p)ᵇ =  ⊡(⊡(pᵇ ⟶ ⊡pᵇ) ⟶ pᵇ) ⟶ pᵇ := by simp [Axioms.Grz, imp_def, box_def];

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
  | hdia p ihp => exact iff_trans''! (dia_iff! ihp) iff_dia_diadot!;
  | hand p q ihp ihq => exact and_replace_iff! ihp ihq;
  | hor p q ihp ihq => exact or_replace_iff! ihp ihq;
  | _ => dsimp [BoxdotTranslation]; exact iff_id!;

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

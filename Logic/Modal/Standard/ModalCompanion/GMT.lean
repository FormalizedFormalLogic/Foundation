import Logic.Modal.Standard.ModalCompanion.Basic
import Logic.Propositional.Superintuitionistic.Kripke.DP
import Logic.Modal.Standard.Kripke.Geach

namespace LO.Modal.Standard

open System FiniteContext
open Necessitation
open LO.Propositional

variable {α : Type u} [DecidableEq α] [Inhabited α] [Encodable α]

variable {iΛ : Superintuitionistic.DeductionParameter α} {mΛ : DeductionParameter α}
variable {p q r : Superintuitionistic.Formula α}

lemma axiomTc_GTranslate! [System.K4 mΛ] : mΛ ⊢! pᵍ ⟶ □pᵍ := by
  induction p using Superintuitionistic.Formula.rec' with
  | hverum => exact dhyp! (nec! verum!);
  | hfalsum => simp only [GoedelTranslation, efq!];
  | hand p q ihp ihq =>
    simp only [GoedelTranslation];
    exact imp_trans''! (and_replace! ihp ihq) collect_box_and!
  | hor p q ihp ihq =>
    simp only [GoedelTranslation];
    exact imp_trans''! (or₃''! (imply_left_or'! ihp) (imply_right_or'! ihq)) collect_box_or!
  | _ => simp only [GoedelTranslation, axiomFour!];

instance [System.S4 mΛ] : System.K4 mΛ where

private lemma provable_efq_of_provable_S4.case_imply₁ [System.K4 mΛ] : mΛ ⊢! (p ⟶ q ⟶ p)ᵍ := by
  simp only [GoedelTranslation];
  exact nec! $ imp_trans''! axiomTc_GTranslate! $ axiomK'! $ nec! $ imply₁!;

private lemma provable_efq_of_provable_S4.case_imply₂ [System.S4 mΛ] : mΛ ⊢! ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)ᵍ := by
  simp only [GoedelTranslation];
  apply nec! $ imp_trans''! (imp_trans''! (axiomK'! $ nec! ?b) axiomFour!) $ axiomK'! $ nec! $ imp_trans''! (axiomK'! $ nec! imply₂!) axiomK!;
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  apply deduct_iff.mpr;
  have : [pᵍ, pᵍ ⟶ □(qᵍ ⟶ rᵍ)] ⊢[mΛ]! pᵍ := by_axm!;
  have : [pᵍ, pᵍ ⟶ □(qᵍ ⟶ rᵍ)] ⊢[mΛ]! (pᵍ ⟶ □(qᵍ ⟶ rᵍ)) := by_axm!;
  have : [pᵍ, pᵍ ⟶ □(qᵍ ⟶ rᵍ)] ⊢[mΛ]! □(qᵍ ⟶ rᵍ) := (by assumption) ⨀ (by assumption);
  exact axiomT'! this;

private lemma provable_efq_of_provable_S4.case_and₃ [System.K4 mΛ] : mΛ ⊢! (p ⟶ q ⟶ p ⋏ q)ᵍ := by
  simp only [GoedelTranslation];
  exact nec! $ imp_trans''! axiomTc_GTranslate! $ axiomK'! $ nec! $ and₃!

private lemma provable_efq_of_provable_S4.case_or₃ [System.K4 mΛ] : mΛ ⊢! (((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)))ᵍ := by
  simp only [GoedelTranslation];
  exact nec! $ imp_trans''! axiomFour! $ axiomK'! $ nec! $ imp_trans''! (axiomK'! $ nec! $ or₃!) axiomK!;

private lemma provable_efq_of_provable_S4.case_neg_equiv [System.K4 mΛ] : mΛ ⊢! (Axioms.NegEquiv p)ᵍ := by
  simp only [GoedelTranslation];
  apply and₃'!;
  . exact nec! $ axiomK'! $ nec! $ and₁'! neg_equiv!;
  . exact nec! $ axiomK'! $ nec! $ and₂'! neg_equiv!;

open provable_efq_of_provable_S4 in
lemma provable_efq_of_provable_S4 (h : 𝐈𝐧𝐭 ⊢! p) : 𝐒𝟒 ⊢! pᵍ := by
  induction h.some with
  | eaxm ih =>
    simp_all only [Set.mem_setOf_eq];
    obtain ⟨p, hp⟩ := ih; subst hp;
    exact nec! efq!;
  | mdp hpq hp ihpq ihp =>
    exact axiomT'! $ axiomK''! (by simpa using ihpq ⟨hpq⟩) $ nec! $ ihp ⟨hp⟩;
  | and₁ => simp only [GoedelTranslation]; exact nec! and₁!;
  | and₂ => simp only [GoedelTranslation]; exact nec! and₂!;
  | or₁ => simp only [GoedelTranslation]; exact nec! or₁!;
  | or₂ => simp only [GoedelTranslation]; exact nec! or₂!;
  | verum => apply verum!;
  | imply₁ => exact case_imply₁;
  | imply₂ => exact case_imply₂;
  | and₃ => exact case_and₃;
  | or₃ => exact case_or₃;
  | neg_equiv => exact case_neg_equiv;

open Kripke

open LO.Kripke
open Formula


-- set_option diagnostics true in
-- set_option diagnostics true
lemma provable_S4_of_provable_efq : (𝐒𝟒 ⊢! pᵍ) → (𝐈𝐧𝐭 ⊢! p) := by
  contrapose;
  intro h;

  -- TOOD: なぜかこれは `Semantics (Superintuitionistic.Formula α) (FrameClass.Dep α)` のsynthが出来ず失敗する．
  -- replace h := (not_imp_not.mpr $ Superintuitionistic.Kripke.Int_complete (α := α) |>.complete) h;

  replace h := (not_imp_not.mpr $ Superintuitionistic.Kripke.Int_complete_aux (α := α)) h;
  simp [Superintuitionistic.Formula.Kripke.ValidOnFrame, Superintuitionistic.Formula.Kripke.ValidOnModel] at h;
  obtain ⟨F, F_refl, F_trans, V, V_hered, w, hp⟩ := h;

  have h₁ : ∀ q x, Superintuitionistic.Formula.Kripke.Satisfies ⟨F, V⟩ x q ↔ (Modal.Standard.Formula.Kripke.Satisfies ⟨F, V⟩ x (qᵍ)) := by
    intro q x;
    induction q using Superintuitionistic.Formula.rec' generalizing x with
    | hatom a =>
      simp [GoedelTranslation];
      constructor;
      . intro _ _ h; exact V_hered h (by assumption);
      . intro h; exact h x (F_refl x);
    | hor p q ihp ihq =>
      simp only [GoedelTranslation];
      constructor;
      . rintro (hp | hq);
        . apply Formula.Kripke.Satisfies.or_def.mpr; left;
          exact ihp x |>.mp hp;
        . apply Formula.Kripke.Satisfies.or_def.mpr; right;
          exact ihq x |>.mp hq;
      . intro h;
        rcases Formula.Kripke.Satisfies.or_def.mp h with (hp | hq)
        . left; exact ihp x |>.mpr hp;
        . right; exact ihq x |>.mpr hq;
    | _ =>
      simp_all [Superintuitionistic.Formula.Kripke.Satisfies, Modal.Standard.Formula.Kripke.Satisfies];
  have : ¬(Modal.Standard.Formula.Kripke.Satisfies ⟨F, V⟩ w (pᵍ)) := (h₁ p w).not.mp hp;

  apply not_imp_not.mpr $ Modal.Standard.Kripke.sound_S4.sound;
  simp [Formula.Kripke.ValidOnFrame, Kripke.ValidOnModel];
  use F;
  exact ⟨⟨F_refl, F_trans⟩, by use V, w⟩;

/-- a.k.a. _Gödel-McKinsey-Tarski Theorem_ -/
theorem provable_efq_iff_provable_S4 : 𝐈𝐧𝐭 ⊢! p ↔ 𝐒𝟒 ⊢! pᵍ := ⟨provable_efq_of_provable_S4, provable_S4_of_provable_efq⟩
instance : ModalCompanion (α := α) 𝐈𝐧𝐭 𝐒𝟒 := ⟨provable_efq_iff_provable_S4⟩


lemma dp_of_mdp [ModalDisjunctive mΛ] [ModalCompanion iΛ mΛ] [System.S4 mΛ] : iΛ ⊢! p ⋎ q → iΛ ⊢! p ∨ iΛ ⊢! q := by
    intro hpq;
    have : mΛ ⊢! □pᵍ ⋎ □qᵍ := or₃'''! (imply_left_or'! axiomTc_GTranslate!) (imply_right_or'! axiomTc_GTranslate!) (by simpa using ModalCompanion.companion.mp hpq);
    cases ModalDisjunctive.modal_disjunctive this with
    | inl h => left; exact ModalCompanion.companion.mpr h;
    | inr h => right; exact ModalCompanion.companion.mpr h;

theorem disjunctive_of_modalDisjunctive [ModalDisjunctive mΛ] [ModalCompanion iΛ mΛ] [System.S4 mΛ] : Disjunctive iΛ := ⟨dp_of_mdp (iΛ := iΛ) (mΛ := mΛ)⟩

end LO.Modal.Standard

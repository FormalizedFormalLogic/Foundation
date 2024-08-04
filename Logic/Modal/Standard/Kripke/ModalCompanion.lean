import Logic.Propositional.Superintuitionistic.Kripke.DP
import Logic.Modal.Standard.Kripke.Geach

namespace LO.Modal.Standard

open System FiniteContext
open Necessitation
open LO.Propositional

variable [DecidableEq α] [Inhabited α] [Encodable α]

/-- Gödel Translation -/
def GoedelTranslation : Superintuitionistic.Formula α → Formula α
  | .atom a  => □(Formula.atom a)
  | ⊤ => ⊤
  | ⊥ => ⊥
  | p ⋏ q => (GoedelTranslation p) ⋏ (GoedelTranslation q)
  | p ⋎ q  => (GoedelTranslation p) ⋎ (GoedelTranslation q)
  | ~p   => □(~(GoedelTranslation p))
  | p ⟶ q => □((GoedelTranslation p) ⟶ (GoedelTranslation q))

postfix:90 "ᵍ" => GoedelTranslation


class ModalCompanion (i𝓓 : Superintuitionistic.DeductionParameter α) (m𝓓 : Modal.Standard.DeductionParameter α) where
  companion : ∀ {p : Superintuitionistic.Formula α}, i𝓓 ⊢! p ↔ m𝓓 ⊢! pᵍ

variable {i𝓓 : Superintuitionistic.DeductionParameter α} {m𝓓 : DeductionParameter α}
variable {p q r : Superintuitionistic.Formula α}

lemma axiomTc_GTranslate! [System.K4 m𝓓] : m𝓓 ⊢! pᵍ ⟶ □pᵍ := by
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

instance [System.S4 m𝓓] : System.K4 m𝓓 where

private lemma provable_efq_of_provable_S4.case_imply₁ [System.K4 m𝓓] : m𝓓 ⊢! (p ⟶ q ⟶ p)ᵍ := by
  simp only [GoedelTranslation];
  exact nec! $ imp_trans''! axiomTc_GTranslate! $ axiomK'! $ nec! $ imply₁!;

private lemma provable_efq_of_provable_S4.case_imply₂ [System.S4 m𝓓] : m𝓓 ⊢! ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)ᵍ := by
  simp only [GoedelTranslation];
  apply nec! $ imp_trans''! (imp_trans''! (axiomK'! $ nec! ?b) axiomFour!) $ axiomK'! $ nec! $ imp_trans''! (axiomK'! $ nec! imply₂!) axiomK!;
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  apply deduct_iff.mpr;
  have : [pᵍ, pᵍ ⟶ □(qᵍ ⟶ rᵍ)] ⊢[m𝓓]! pᵍ := by_axm!;
  have : [pᵍ, pᵍ ⟶ □(qᵍ ⟶ rᵍ)] ⊢[m𝓓]! (pᵍ ⟶ □(qᵍ ⟶ rᵍ)) := by_axm!;
  have : [pᵍ, pᵍ ⟶ □(qᵍ ⟶ rᵍ)] ⊢[m𝓓]! □(qᵍ ⟶ rᵍ) := (by assumption) ⨀ (by assumption);
  exact axiomT'! this;

private lemma provable_efq_of_provable_S4.case_and₃ [System.K4 m𝓓] : m𝓓 ⊢! (p ⟶ q ⟶ p ⋏ q)ᵍ := by
  simp only [GoedelTranslation];
  exact nec! $ imp_trans''! axiomTc_GTranslate! $ axiomK'! $ nec! $ and₃!

private lemma provable_efq_of_provable_S4.case_or₃ [System.K4 m𝓓] : m𝓓 ⊢! (((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)))ᵍ := by
  simp only [GoedelTranslation];
  exact nec! $ imp_trans''! axiomFour! $ axiomK'! $ nec! $ imp_trans''! (axiomK'! $ nec! $ or₃!) axiomK!;

private lemma provable_efq_of_provable_S4.case_neg_equiv [System.K4 m𝓓] : m𝓓 ⊢! (Axioms.NegEquiv p)ᵍ := by
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

open Superintuitionistic.Kripke
open Superintuitionistic.Formula.Kripke

open Kripke

open Formula

lemma provable_S4_of_provable_efq : (𝐒𝟒 ⊢! pᵍ) → (𝐈𝐧𝐭 ⊢! p) := by
  contrapose;
  intro h;
  replace h := (not_imp_not.mpr $ Superintuitionistic.Kripke.Int_Complete.complete) h;
  simp [Semantics.Realize, ValidOnFrame, ValidOnModel] at h;
  obtain ⟨IF, ⟨IF_refl, IF_trans⟩, IV, IV_hered, w, hp⟩ := h;

  let M : Modal.Standard.Kripke.Model α := { Frame := { Rel := IF.Rel, }, Valuation := IV };

  have h₁ : ∀ q v, Satisfies ⟨IF, IV⟩ v q ↔ (Modal.Standard.Formula.Kripke.Satisfies M v (qᵍ)) := by
    intro q v;
    induction q using Superintuitionistic.Formula.rec' generalizing v with
    | hatom a =>
      constructor;
      . intro _ _ h;
        simp_all only [Satisfies.iff_models, Satisfies, Formula.Kripke.Satisfies];
        exact IV_hered h (by assumption);
      . intro h;
        simpa only [Satisfies.iff_models, Satisfies, Formula.Kripke.Satisfies] using h $ IF_refl v;
    | _ => simp_all only [Satisfies, Kripke.Satisfies];
  have : ¬(Modal.Standard.Formula.Kripke.Satisfies M w (pᵍ)) := (h₁ p w).not.mp hp;

  apply not_imp_not.mpr $ Modal.Standard.Kripke.sound_S4.sound;
  simp [Formula.Kripke.ValidOnFrame, Kripke.ValidOnModel];
  use M.Frame;
  exact ⟨
    IF_refl,
    IF_trans,
    by use M.Valuation, w
  ⟩;

/-- a.k.a. _Gödel-McKinsey-Tarski Theorem_ -/
theorem provable_efq_iff_provable_S4 : 𝐈𝐧𝐭 ⊢! p ↔ 𝐒𝟒 ⊢! pᵍ := ⟨provable_efq_of_provable_S4, provable_S4_of_provable_efq⟩
instance : ModalCompanion (α := α) 𝐈𝐧𝐭 𝐒𝟒 := ⟨provable_efq_iff_provable_S4⟩


lemma dp_of_mdp [ModalDisjunctive m𝓓] [ModalCompanion i𝓓 m𝓓] [System.S4 m𝓓] : i𝓓 ⊢! p ⋎ q → i𝓓 ⊢! p ∨ i𝓓 ⊢! q := by
    intro hpq;
    have : m𝓓 ⊢! □pᵍ ⋎ □qᵍ := or₃'''! (imply_left_or'! axiomTc_GTranslate!) (imply_right_or'! axiomTc_GTranslate!) (by simpa using ModalCompanion.companion.mp hpq);
    cases ModalDisjunctive.modal_disjunctive this with
    | inl h => left; exact ModalCompanion.companion.mpr h;
    | inr h => right; exact ModalCompanion.companion.mpr h;

theorem disjunctive_of_modalDisjunctive [ModalDisjunctive m𝓓] [ModalCompanion i𝓓 m𝓓] [System.S4 m𝓓] : Disjunctive i𝓓 := ⟨dp_of_mdp (i𝓓 := i𝓓) (m𝓓 := m𝓓)⟩

end LO.Modal.Standard

import Logic.Logic.Disjunctive
import Logic.IntProp.Deduction
import Logic.Modal.Hilbert

namespace LO.Modal

open System FiniteContext
open Necessitation
open IntProp

/-- Gödel Translation -/
def GoedelTranslation : IntProp.Formula α → Modal.Formula α
  | .atom a  => □(Formula.atom a)
  | ⊤ => ⊤
  | ⊥ => ⊥
  | ∼p => □(∼(GoedelTranslation p))
  | p ⋏ q => (GoedelTranslation p) ⋏ (GoedelTranslation q)
  | p ⋎ q => (GoedelTranslation p) ⋎ (GoedelTranslation q)
  | p ➝ q => □((GoedelTranslation p) ➝ (GoedelTranslation q))
postfix:90 "ᵍ" => GoedelTranslation

class ModalCompanion (iΛ : IntProp.Hilbert α) (mΛ : Modal.Hilbert α) where
  companion : ∀ {p : IntProp.Formula α}, iΛ ⊢! p ↔ mΛ ⊢! pᵍ

variable {α : Type u} [DecidableEq α] [Inhabited α] [Encodable α]
variable {iΛ : IntProp.Hilbert α} {mΛ : Hilbert α}
variable {p q r : IntProp.Formula α}

lemma axiomTc_GTranslate! [System.K4 mΛ] : mΛ ⊢! pᵍ ➝ □pᵍ := by
  induction p using IntProp.Formula.rec' with
  | hverum => exact dhyp! (nec! verum!);
  | hfalsum => simp only [GoedelTranslation, efq!];
  | hand p q ihp ihq =>
    simp only [GoedelTranslation];
    exact imp_trans''! (and_replace! ihp ihq) collect_box_and!
  | hor p q ihp ihq =>
    simp only [GoedelTranslation];
    exact imp_trans''! (or₃''! (imply_left_or'! ihp) (imply_right_or'! ihq)) collect_box_or!
  | _ => simp only [GoedelTranslation, axiomFour!];


section

private lemma provable_efq_of_provable_S4.case_imply₁ [System.K4 mΛ] : mΛ ⊢! (p ➝ q ➝ p)ᵍ := by
  simp only [GoedelTranslation];
  exact nec! $ imp_trans''! axiomTc_GTranslate! $ axiomK'! $ nec! $ imply₁!;

private lemma provable_efq_of_provable_S4.case_imply₂ [System.S4 mΛ] : mΛ ⊢! ((p ➝ q ➝ r) ➝ (p ➝ q) ➝ p ➝ r)ᵍ := by
  simp only [GoedelTranslation];
  apply nec! $ imp_trans''! (imp_trans''! (axiomK'! $ nec! ?b) axiomFour!) $ axiomK'! $ nec! $ imp_trans''! (axiomK'! $ nec! imply₂!) axiomK!;
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  apply deduct_iff.mpr;
  have : [pᵍ, pᵍ ➝ □(qᵍ ➝ rᵍ)] ⊢[mΛ]! pᵍ := by_axm!;
  have : [pᵍ, pᵍ ➝ □(qᵍ ➝ rᵍ)] ⊢[mΛ]! (pᵍ ➝ □(qᵍ ➝ rᵍ)) := by_axm!;
  have : [pᵍ, pᵍ ➝ □(qᵍ ➝ rᵍ)] ⊢[mΛ]! □(qᵍ ➝ rᵍ) := (by assumption) ⨀ (by assumption);
  exact axiomT'! this;
private lemma provable_efq_of_provable_S4.case_and₃ [System.K4 mΛ] : mΛ ⊢! (p ➝ q ➝ p ⋏ q)ᵍ := by
  simp only [GoedelTranslation];
  exact nec! $ imp_trans''! axiomTc_GTranslate! $ axiomK'! $ nec! $ and₃!

private lemma provable_efq_of_provable_S4.case_or₃ [System.K4 mΛ] : mΛ ⊢! (((p ➝ r) ➝ (q ➝ r) ➝ (p ⋎ q ➝ r)))ᵍ := by
  simp only [GoedelTranslation];
  exact nec! $ imp_trans''! axiomFour! $ axiomK'! $ nec! $ imp_trans''! (axiomK'! $ nec! $ or₃!) axiomK!;

private lemma provable_efq_of_provable_S4.case_neg_equiv [System.K4 mΛ] : mΛ ⊢! (Axioms.NegEquiv p)ᵍ := by
  simp only [GoedelTranslation];
  apply and₃'!;
  . exact nec! $ axiomK'! $ nec! $ and₁'! neg_equiv!;
  . exact nec! $ axiomK'! $ nec! $ and₂'! neg_equiv!;

instance [System.S4 mΛ] : System.K4 mΛ where

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

end


lemma dp_of_mdp [ModalDisjunctive mΛ] [ModalCompanion iΛ mΛ] [System.S4 mΛ] : iΛ ⊢! p ⋎ q → iΛ ⊢! p ∨ iΛ ⊢! q := by
    intro hpq;
    have : mΛ ⊢! □pᵍ ⋎ □qᵍ := or₃'''! (imply_left_or'! axiomTc_GTranslate!) (imply_right_or'! axiomTc_GTranslate!) (by simpa using ModalCompanion.companion.mp hpq);
    cases ModalDisjunctive.modal_disjunctive this with
    | inl h => left; exact ModalCompanion.companion.mpr h;
    | inr h => right; exact ModalCompanion.companion.mpr h;

theorem disjunctive_of_modalDisjunctive [ModalDisjunctive mΛ] [ModalCompanion iΛ mΛ] [System.S4 mΛ] : Disjunctive iΛ := ⟨dp_of_mdp (iΛ := iΛ) (mΛ := mΛ)⟩

end LO.Modal

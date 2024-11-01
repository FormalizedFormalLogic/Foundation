import Foundation.Logic.Disjunctive
import Foundation.IntProp.Deduction
import Foundation.Modal.Hilbert
import Foundation.Modal.MDP

namespace LO.Modal

open System FiniteContext
open Necessitation
open IntProp

/-- Gödel Translation -/
def GoedelTranslation : IntProp.Formula α → Modal.Formula α
  | .atom a  => □(Formula.atom a)
  | ⊤ => ⊤
  | ⊥ => ⊥
  | ∼φ => □(∼(GoedelTranslation φ))
  | φ ⋏ ψ => (GoedelTranslation φ) ⋏ (GoedelTranslation ψ)
  | φ ⋎ ψ => (GoedelTranslation φ) ⋎ (GoedelTranslation ψ)
  | φ ➝ ψ => □((GoedelTranslation φ) ➝ (GoedelTranslation ψ))
postfix:90 "ᵍ" => GoedelTranslation

class ModalCompanion (iΛ : IntProp.Hilbert α) (mΛ : Modal.Hilbert α) where
  companion : ∀ {φ : IntProp.Formula α}, iΛ ⊢! φ ↔ mΛ ⊢! φᵍ

variable {α : Type u}
variable {iΛ : IntProp.Hilbert α} {mΛ : Hilbert α}
variable {φ ψ χ : IntProp.Formula α}

lemma axiomTc_GTranslate! [DecidableEq α] [System.K4 mΛ] : mΛ ⊢! φᵍ ➝ □φᵍ := by
  induction φ using IntProp.Formula.rec' with
  | hverum => exact imply₁'! (nec! verum!);
  | hfalsum => simp only [GoedelTranslation, efq!];
  | hand φ ψ ihp ihq =>
    simp only [GoedelTranslation];
    exact imp_trans''! (and_replace! ihp ihq) collect_box_and!
  | hor φ ψ ihp ihq =>
    simp only [GoedelTranslation];
    exact imp_trans''! (or₃''! (imply_left_or'! ihp) (imply_right_or'! ihq)) collect_box_or!
  | _ => simp only [GoedelTranslation, axiomFour!];


section

private lemma provable_efq_of_provable_S4.case_imply₁ [DecidableEq α] [System.K4 mΛ] : mΛ ⊢! (φ ➝ ψ ➝ φ)ᵍ := by
  simp only [GoedelTranslation];
  exact nec! $ imp_trans''! axiomTc_GTranslate! $ axiomK'! $ nec! $ imply₁!;

private lemma provable_efq_of_provable_S4.case_imply₂ [DecidableEq α] [System.S4 mΛ] : mΛ ⊢! ((φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ)ᵍ := by
  simp only [GoedelTranslation];
  apply nec! $ imp_trans''! (imp_trans''! (axiomK'! $ nec! ?b) axiomFour!) $ axiomK'! $ nec! $ imp_trans''! (axiomK'! $ nec! imply₂!) axiomK!;
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  apply deduct_iff.mpr;
  have : [φᵍ, φᵍ ➝ □(ψᵍ ➝ χᵍ)] ⊢[mΛ]! φᵍ := by_axm!;
  have : [φᵍ, φᵍ ➝ □(ψᵍ ➝ χᵍ)] ⊢[mΛ]! (φᵍ ➝ □(ψᵍ ➝ χᵍ)) := by_axm!;
  have : [φᵍ, φᵍ ➝ □(ψᵍ ➝ χᵍ)] ⊢[mΛ]! □(ψᵍ ➝ χᵍ) := (by assumption) ⨀ (by assumption);
  exact axiomT'! this;
private lemma provable_efq_of_provable_S4.case_and₃ [DecidableEq α] [System.K4 mΛ] : mΛ ⊢! (φ ➝ ψ ➝ φ ⋏ ψ)ᵍ := by
  simp only [GoedelTranslation];
  exact nec! $ imp_trans''! axiomTc_GTranslate! $ axiomK'! $ nec! $ and₃!

private lemma provable_efq_of_provable_S4.case_or₃ [System.K4 mΛ] : mΛ ⊢! (((φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ)))ᵍ := by
  simp only [GoedelTranslation];
  exact nec! $ imp_trans''! axiomFour! $ axiomK'! $ nec! $ imp_trans''! (axiomK'! $ nec! $ or₃!) axiomK!;

private lemma provable_efq_of_provable_S4.case_neg_equiv [System.K4 mΛ] : mΛ ⊢! (Axioms.NegEquiv φ)ᵍ := by
  simp only [GoedelTranslation];
  apply and₃'!;
  . exact nec! $ axiomK'! $ nec! $ and₁'! neg_equiv!;
  . exact nec! $ axiomK'! $ nec! $ and₂'! neg_equiv!;

instance [System.S4 mΛ] : System.K4 mΛ where

open provable_efq_of_provable_S4 in
lemma provable_efq_of_provable_S4 [DecidableEq α] (h : 𝐈𝐧𝐭 ⊢! φ) : 𝐒𝟒 ⊢! φᵍ := by
  induction h.some with
  | eaxm ih =>
    simp_all only [Set.mem_setOf_eq];
    obtain ⟨φ, hp⟩ := ih; subst hp;
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


lemma dp_of_mdp [DecidableEq α] [ModalDisjunctive mΛ] [ModalCompanion iΛ mΛ] [System.S4 mΛ] : iΛ ⊢! φ ⋎ ψ → iΛ ⊢! φ ∨ iΛ ⊢! ψ := by
    intro hpq;
    have : mΛ ⊢! □φᵍ ⋎ □ψᵍ := or₃'''! (imply_left_or'! axiomTc_GTranslate!) (imply_right_or'! axiomTc_GTranslate!) (by simpa using ModalCompanion.companion.mp hpq);
    cases ModalDisjunctive.modal_disjunctive this with
    | inl h => left; exact ModalCompanion.companion.mpr h;
    | inr h => right; exact ModalCompanion.companion.mpr h;

theorem disjunctive_of_modalDisjunctive [DecidableEq α] [ModalDisjunctive mΛ] [ModalCompanion iΛ mΛ] [System.S4 mΛ] : Disjunctive iΛ := ⟨dp_of_mdp (iΛ := iΛ) (mΛ := mΛ)⟩

end LO.Modal

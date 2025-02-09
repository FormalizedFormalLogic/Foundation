import Foundation.Logic.Disjunctive
import Foundation.IntProp.Hilbert.WellKnown
import Foundation.Modal.Hilbert.WellKnown

namespace LO.Modal

open System FiniteContext
open Necessitation
open IntProp

/-- Gödel Translation -/
def GoedelTranslation : IntProp.Formula α → Modal.Formula α
  | .atom a  => □(Formula.atom a)
  | ⊥ => ⊥
  | φ ⋏ ψ => (GoedelTranslation φ) ⋏ (GoedelTranslation ψ)
  | φ ⋎ ψ => (GoedelTranslation φ) ⋎ (GoedelTranslation ψ)
  | φ ➝ ψ => □((GoedelTranslation φ) ➝ (GoedelTranslation ψ))
postfix:90 "ᵍ" => GoedelTranslation

class ModalCompanion (iH : IntProp.Hilbert α) (mH : Modal.Hilbert α) where
  companion : ∀ {φ : IntProp.Formula α}, iH ⊢! φ ↔ mH ⊢! φᵍ

variable {iH : IntProp.Hilbert ℕ} {mH : Modal.Hilbert ℕ}
variable {φ ψ χ : IntProp.Formula ℕ}

lemma axiomTc_GTranslate! [System.K4 mH] : mH ⊢! φᵍ ➝ □φᵍ := by
  induction φ using IntProp.Formula.rec' with
  | hfalsum => simp only [GoedelTranslation, efq!];
  | hand φ ψ ihp ihq =>
    simp only [GoedelTranslation];
    exact imp_trans''! (and_replace! ihp ihq) collect_box_and!
  | hor φ ψ ihp ihq =>
    simp only [GoedelTranslation];
    exact imp_trans''! (or₃''! (imply_left_or'! ihp) (imply_right_or'! ihq)) collect_box_or!
  | _ => simp only [GoedelTranslation, axiomFour!];


section

private lemma provable_efq_of_provable_S4.case_imply₁ [System.K4 mH] : mH ⊢! (φ ➝ ψ ➝ φ)ᵍ := by
  dsimp [GoedelTranslation];
  exact nec! $ imp_trans''! axiomTc_GTranslate! $ axiomK'! $ nec! $ imply₁!;

private lemma provable_efq_of_provable_S4.case_imply₂ [System.S4 mH] : mH ⊢! ((φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ)ᵍ := by
  dsimp [GoedelTranslation];
  apply nec! $ imp_trans''! (imp_trans''! (axiomK'! $ nec! ?b) axiomFour!) $ axiomK'! $ nec! $ imp_trans''! (axiomK'! $ nec! imply₂!) axiomK!;
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  apply deduct_iff.mpr;
  have : [φᵍ, φᵍ ➝ □(ψᵍ ➝ χᵍ)] ⊢[mH]! φᵍ := by_axm!;
  have : [φᵍ, φᵍ ➝ □(ψᵍ ➝ χᵍ)] ⊢[mH]! (φᵍ ➝ □(ψᵍ ➝ χᵍ)) := by_axm!;
  have : [φᵍ, φᵍ ➝ □(ψᵍ ➝ χᵍ)] ⊢[mH]! □(ψᵍ ➝ χᵍ) := (by assumption) ⨀ (by assumption);
  exact axiomT'! this;
private lemma provable_efq_of_provable_S4.case_and₃ [System.K4 mH] : mH ⊢! (φ ➝ ψ ➝ φ ⋏ ψ)ᵍ := by
  dsimp [GoedelTranslation];
  exact nec! $ imp_trans''! axiomTc_GTranslate! $ axiomK'! $ nec! $ and₃!

private lemma provable_efq_of_provable_S4.case_or₃ [System.K4 mH] : mH ⊢! (((φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ)))ᵍ := by
  dsimp [GoedelTranslation];
  exact nec! $ imp_trans''! axiomFour! $ axiomK'! $ nec! $ imp_trans''! (axiomK'! $ nec! $ or₃!) axiomK!;

open provable_efq_of_provable_S4 in
lemma provable_efq_of_provable_S4 (h : (IntProp.Hilbert.Int) ⊢! φ) : (Hilbert.S4) ⊢! φᵍ := by
  induction h using IntProp.Hilbert.Deduction.rec! with
  | maxm ih =>
    rcases (by simpa using ih) with ⟨_, rfl⟩;
    exact nec! efq!;
  | mdp ihpq ihp =>
    exact axiomT'! $ axiomK''! (ihpq) $ nec! $ ihp;
  | verum => exact nec! imp_id!;
  | andElimL => exact nec! and₁!;
  | andElimR => exact nec! and₂!;
  | andIntro => exact case_and₃;
  | orIntroL => exact nec! or₁!;
  | orIntroR => exact nec! or₂!;
  | orElim => exact case_or₃;
  | implyS => exact case_imply₁;
  | implyK => exact case_imply₂;

end


lemma dp_of_mdp [ModalDisjunctive mH] [ModalCompanion iH mH] [System.S4 mH] : iH ⊢! φ ⋎ ψ → iH ⊢! φ ∨ iH ⊢! ψ := by
    intro hpq;
    have : mH ⊢! □φᵍ ⋎ □ψᵍ := or₃'''! (imply_left_or'! axiomTc_GTranslate!) (imply_right_or'! axiomTc_GTranslate!) (by simpa using ModalCompanion.companion.mp hpq);
    cases ModalDisjunctive.modal_disjunctive this with
    | inl h => left; exact ModalCompanion.companion.mpr h;
    | inr h => right; exact ModalCompanion.companion.mpr h;

theorem disjunctive_of_modalDisjunctive [ModalDisjunctive mH] [ModalCompanion iH mH] [System.S4 mH] : Disjunctive iH := ⟨dp_of_mdp (iH := iH) (mH := mH)⟩

end LO.Modal

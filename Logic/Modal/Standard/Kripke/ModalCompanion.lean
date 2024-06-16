import Logic.Propositional.Superintuitionistic.Kripke.Semantics
import Logic.Propositional.Superintuitionistic.Kripke.DP
import Logic.Modal.Standard.Deduction
import Logic.Modal.Standard.HilbertStyle
import Logic.Modal.Standard.Kripke.Semantics
import Logic.Modal.Standard.Kripke.Soundness
import Logic.Modal.Standard.Kripke.Geach.Definability

namespace LO.System

variable {F : Type*} [StandardModalLogicalConnective F]
variable {S : Type*} [System F S]

class ModalDisjunctive (𝓢 : S) : Prop where
  modal_disjunctive : ∀ {p q : F}, 𝓢 ⊢! □p ⋎ □q → 𝓢 ⊢! p ∨ 𝓢 ⊢! q

end LO.System


namespace LO.Modal.Standard

open System FiniteContext
open Necessitation
open LO.Propositional

variable [DecidableEq α] [Inhabited α] [Encodable α]

/-- Gödel Translation -/
def GoedelTranslation : Superintuitionistic.Formula α → Formula α
  | .atom a  => □(Formula.atom a)
  | .verum   => ⊤
  | .falsum  => ⊥
  | .and p q => (GoedelTranslation p) ⋏ (GoedelTranslation q)
  | .or p q  => (GoedelTranslation p) ⋎ (GoedelTranslation q)
  | .imp p q => □((GoedelTranslation p) ⟶ (GoedelTranslation q))

postfix:75 "ᵍ" => GoedelTranslation

namespace GoedelTranslation

variable {p q : Superintuitionistic.Formula α}

@[simp] lemma atom_def : (Superintuitionistic.Formula.atom a)ᵍ = □(Formula.atom a) := by simp [GoedelTranslation];
@[simp] lemma falsum_def : (⊥ : Superintuitionistic.Formula α)ᵍ = ⊥ := by simp [GoedelTranslation];
@[simp] lemma verum_def : (⊤ : Superintuitionistic.Formula α)ᵍ = ⊤ := by simp [GoedelTranslation];
@[simp] lemma and_def : (p ⋏ q)ᵍ = pᵍ ⋏ qᵍ := by simp [GoedelTranslation];
@[simp] lemma or_def : (p ⋎ q)ᵍ = pᵍ ⋎ qᵍ := by simp [GoedelTranslation];
@[simp] lemma imp_def : (p ⟶ q)ᵍ = □(pᵍ ⟶ qᵍ) := by simp [GoedelTranslation];
@[simp] lemma neg_def' : (~p)ᵍ = □~(p)ᵍ := by simp [GoedelTranslation, NegAbbrev.neg];

end GoedelTranslation

class ModalCompanion (i𝓓 : Superintuitionistic.DeductionParameter α) (m𝓓 : Modal.Standard.DeductionParameter α) where
  companion : ∀ {p : Superintuitionistic.Formula α}, i𝓓 ⊢! p ↔ m𝓓 ⊢! pᵍ

variable {i𝓓 : Superintuitionistic.DeductionParameter α} {m𝓓 : DeductionParameter α}
variable {p q r : Superintuitionistic.Formula α}

lemma axiomTc_GTranslate! [System.K4 m𝓓] : m𝓓 ⊢! pᵍ ⟶ □pᵍ := by
  induction p using Superintuitionistic.Formula.rec' with
  | hatom => simp only [GoedelTranslation.atom_def, axiomFour!];
  | himp => simp only [GoedelTranslation.imp_def, axiomFour!];
  | hfalsum => simp only [GoedelTranslation.falsum_def, efq!];
  | hverum => exact dhyp! (nec! verum!);
  | hand p q ihp ihq =>
    simp only [GoedelTranslation.and_def];
    exact imp_trans! (andReplace! ihp ihq) collect_box_and!
  | hor p q ihp ihq =>
    simp only [GoedelTranslation.or_def];
    exact imp_trans! (or₃''! (implyOrLeft'! ihp) (implyOrRight'! ihq)) collect_box_or!

instance [System.S4 m𝓓] : System.K4 m𝓓 where

private lemma provable_efq_of_provable_S4.case_imply₁ [System.K4 m𝓓] : m𝓓 ⊢! (p ⟶ q ⟶ p)ᵍ := by
  simp only [GoedelTranslation.imp_def];
  exact nec! $ imp_trans! axiomTc_GTranslate! $ axiomK'! $ nec! $ imply₁!;

private lemma provable_efq_of_provable_S4.case_imply₂ [System.S4 m𝓓] : m𝓓 ⊢! ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)ᵍ := by
  simp only [GoedelTranslation.imp_def];
  refine nec! $ imp_trans! (imp_trans! (axiomK'! $ nec! ?b) axiomFour!) $ axiomK'! $ nec! $ imp_trans! (axiomK'! $ nec! imply₂!) axiomK!;
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  apply deduct_iff.mpr;
  have : [pᵍ, pᵍ ⟶ □(qᵍ ⟶ rᵍ)] ⊢[m𝓓]! pᵍ := by_axm! (by simp);
  have : [pᵍ, pᵍ ⟶ □(qᵍ ⟶ rᵍ)] ⊢[m𝓓]! (pᵍ ⟶ □(qᵍ ⟶ rᵍ)) := by_axm! (by simp);
  have : [pᵍ, pᵍ ⟶ □(qᵍ ⟶ rᵍ)] ⊢[m𝓓]! □(qᵍ ⟶ rᵍ) := (by assumption) ⨀ (by assumption);
  exact axiomT'! this;

private lemma provable_efq_of_provable_S4.case_and₃ [System.K4 m𝓓] : m𝓓 ⊢! (p ⟶ q ⟶ p ⋏ q)ᵍ := by
  simp only [GoedelTranslation.imp_def, GoedelTranslation.and_def];
  exact nec! $ imp_trans! axiomTc_GTranslate! $ axiomK'! $ nec! $ and₃!

private lemma provable_efq_of_provable_S4.case_or₃ [System.K4 m𝓓] : m𝓓 ⊢! (((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)))ᵍ := by
  simp only [GoedelTranslation.imp_def, GoedelTranslation.or_def];
  exact nec! $ imp_trans! axiomFour! $ axiomK'! $ nec! $ imp_trans! (axiomK'! $ nec! $ or₃!) axiomK!;

open provable_efq_of_provable_S4 in
lemma provable_efq_of_provable_S4 (h : 𝐈𝐧𝐭 ⊢! p) : 𝐒𝟒 ⊢! pᵍ := by
  induction h.some with
  | eaxm ih =>
    simp_all only [Set.mem_setOf_eq];
    obtain ⟨p, hp⟩ := ih; subst hp;
    exact nec! efq!;
  | mdp hpq hp ihpq ihp =>
    exact axiomT'! $ axiomK''! (by simpa using ihpq ⟨hpq⟩) $ nec! $ ihp ⟨hp⟩;
  | verum => apply verum!;
  | imply₁ => exact case_imply₁;
  | imply₂ => exact case_imply₂;
  | and₁ => simp only [GoedelTranslation.imp_def, GoedelTranslation.and_def]; exact nec! and₁!;
  | and₂ => simp only [GoedelTranslation.imp_def, GoedelTranslation.and_def]; exact nec! and₂!;
  | and₃ => exact case_and₃;
  | or₁ => simp only [GoedelTranslation.imp_def, GoedelTranslation.or_def]; exact nec! or₁!;
  | or₂ => simp only [GoedelTranslation.imp_def, GoedelTranslation.or_def]; exact nec! or₂!;
  | or₃ => exact case_or₃;

open Superintuitionistic.Kripke
open Superintuitionistic.Formula.Kripke

open Kripke

lemma provable_S4_of_provable_efq : (𝐒𝟒 ⊢! pᵍ) → (𝐈𝐧𝐭 ⊢! p) := by
  contrapose;
  intro h;
  obtain ⟨iF, _, iV, iV_hereditary, w, h⟩ := by simpa [ValidOnFrameClass, ValidOnFrame, ValidOnModel] using not_imp_not.mpr Superintuitionistic.Kripke.complete! h;

  let M : Modal.Standard.Kripke.Model α := { Frame := { Rel := iF.Rel }, Valuation := iV };
  have h₁ : ∀ q v, Satisfies ⟨iF, iV, iV_hereditary⟩ v q ↔ (Modal.Standard.Formula.Kripke.Satisfies M v (qᵍ)) := by
    intro q v;
    induction q using Superintuitionistic.Formula.rec' generalizing v with
    | hatom a =>
      constructor;
      . intro _ _ h;
        simp_all only [Satisfies.iff_models, Satisfies, Formula.Kripke.Satisfies];
        exact iV_hereditary h (by assumption);
      . intro h;
        simpa only [Satisfies.iff_models, Satisfies, Formula.Kripke.Satisfies] using h v $ iF.Rel_refl v;
    | _ => simp_all;
  have : ¬(Modal.Standard.Formula.Kripke.Satisfies M w (pᵍ)) := (h₁ p w).not.mp h;

  apply not_imp_not.mpr $ Modal.Standard.Kripke.sound!_on_frameclass;
  simp [Formula.Kripke.ValidOnFrame, Formula.Kripke.ValidOnModel];
  existsi M.Frame;
  constructor;
  . apply Modal.Standard.Kripke.iff_definability_memAxiomSetFrameClass
      (show Kripke.Definability _ (λ F => Reflexive F.Rel ∧ Transitive F.Rel) by simpa using instGeachDefinability (L := 𝐒𝟒))
      |>.mpr;
    constructor;
    . exact iF.Rel_refl;
    . exact iF.Rel_trans;
  . use M.Valuation, w;

/-- a.k.a. _Gödel-McKinsey-Tarski Theorem_ -/
theorem provable_efq_iff_provable_S4 : 𝐈𝐧𝐭 ⊢! p ↔ 𝐒𝟒 ⊢! pᵍ := ⟨provable_efq_of_provable_S4, provable_S4_of_provable_efq⟩
instance : ModalCompanion (α := α) 𝐈𝐧𝐭 𝐒𝟒 := ⟨provable_efq_iff_provable_S4⟩


lemma dp_of_mdp [ModalDisjunctive m𝓓] [ModalCompanion i𝓓 m𝓓] [S4 m𝓓] : i𝓓 ⊢! p ⋎ q → i𝓓 ⊢! p ∨ i𝓓 ⊢! q := by
    intro hpq;
    have : m𝓓 ⊢! □pᵍ ⋎ □qᵍ := or₃'! (implyOrLeft'! axiomTc_GTranslate!) (implyOrRight'! axiomTc_GTranslate!) (by simpa using ModalCompanion.companion.mp hpq);
    cases ModalDisjunctive.modal_disjunctive this with
    | inl h => left; exact ModalCompanion.companion.mpr h;
    | inr h => right; exact ModalCompanion.companion.mpr h;

theorem disjunctive_of_modalDisjunctive [ModalDisjunctive m𝓓] [ModalCompanion i𝓓 m𝓓] [S4 m𝓓] : Disjunctive i𝓓 := ⟨dp_of_mdp (i𝓓 := i𝓓) (m𝓓 := m𝓓)⟩

end LO.Modal.Standard

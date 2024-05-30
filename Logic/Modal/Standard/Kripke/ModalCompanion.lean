import Logic.Propositional.Superintuitionistic
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

variable [DecidableEq α] [Inhabited α]

/-- Gödel Translation -/
def GTranslation : Superintuitionistic.Formula α → Formula α
  | .atom a  => □(Formula.atom a)
  | .verum   => ⊤
  | .falsum  => ⊥
  | .and p q => (GTranslation p) ⋏ (GTranslation q)
  | .or p q  => (GTranslation p) ⋎ (GTranslation q)
  | .imp p q => □((GTranslation p) ⟶ (GTranslation q))

postfix:75 "ᵍ" => GTranslation

namespace GTranslation

variable {p q : Superintuitionistic.Formula α}

@[simp] lemma atom_def : (Superintuitionistic.Formula.atom a)ᵍ = □(Formula.atom a) := by simp [GTranslation];
@[simp] lemma falsum_def : (⊥ : Superintuitionistic.Formula α)ᵍ = ⊥ := by simp [GTranslation];
@[simp] lemma verum_def : (⊤ : Superintuitionistic.Formula α)ᵍ = ⊤ := by simp [GTranslation];
@[simp] lemma and_def : (p ⋏ q)ᵍ = pᵍ ⋏ qᵍ := by simp [GTranslation];
@[simp] lemma or_def : (p ⋎ q)ᵍ = pᵍ ⋎ qᵍ := by simp [GTranslation];
@[simp] lemma imp_def : (p ⟶ q)ᵍ = □(pᵍ ⟶ qᵍ) := by simp [GTranslation];
@[simp] lemma neg_def' : (~p)ᵍ = □~(p)ᵍ := by simp [GTranslation, NegDefinition.neg];

end GTranslation

class ModalCompanion (iΛ : Superintuitionistic.AxiomSet α) (mL : DeductionParameter α) where
  companion : ∀ {p : Superintuitionistic.Formula α}, iΛ ⊢! p ↔ mL ⊢! pᵍ

variable {iΛ : Superintuitionistic.AxiomSet α} {mL : DeductionParameter α}
variable {p q r : Superintuitionistic.Formula α}

lemma axiomTc_GTranslate! [System.K4 mL] : mL ⊢! pᵍ ⟶ □pᵍ := by
  induction p using Superintuitionistic.Formula.rec' with
  | hatom => simp only [GTranslation.atom_def, axiomFour!];
  | himp => simp only [GTranslation.imp_def, axiomFour!];
  | hfalsum => simp only [GTranslation.falsum_def, efq!];
  | hverum => exact dhyp! (nec! verum!);
  | hand p q ihp ihq =>
    simp only [GTranslation.and_def];
    exact imp_trans! (andReplace! ihp ihq) collect_box_and!
  | hor p q ihp ihq =>
    simp only [GTranslation.or_def];
    exact imp_trans! (disj₃''! (implyOrLeft'! ihp) (implyOrRight'! ihq)) collect_box_or!

instance [System.S4 mL] : System.K4 mL where

private lemma provable_efq_of_provable_S4.case_imply₁ [System.K4 mL] : mL ⊢! (p ⟶ q ⟶ p)ᵍ := by
  simp only [GTranslation.imp_def];
  exact nec! $ imp_trans! axiomTc_GTranslate! $ axiomK'! $ nec! $ imply₁!;

private lemma provable_efq_of_provable_S4.case_imply₂ [System.S4 mL] : mL ⊢! ((p ⟶ q ⟶ r) ⟶ (p ⟶ q) ⟶ p ⟶ r)ᵍ := by
  simp only [GTranslation.imp_def];
  refine nec! $ imp_trans! (imp_trans! (axiomK'! $ nec! ?b) axiomFour!) $ axiomK'! $ nec! $ imp_trans! (axiomK'! $ nec! imply₂!) axiomK!;
  apply provable_iff_provable.mpr;
  apply deduct_iff.mpr;
  apply deduct_iff.mpr;
  have : [pᵍ, pᵍ ⟶ □(qᵍ ⟶ rᵍ)] ⊢[mL]! pᵍ := by_axm! (by simp);
  have : [pᵍ, pᵍ ⟶ □(qᵍ ⟶ rᵍ)] ⊢[mL]! (pᵍ ⟶ □(qᵍ ⟶ rᵍ)) := by_axm! (by simp);
  have : [pᵍ, pᵍ ⟶ □(qᵍ ⟶ rᵍ)] ⊢[mL]! □(qᵍ ⟶ rᵍ) := (by assumption) ⨀ (by assumption);
  exact axiomT'! this;

private lemma provable_efq_of_provable_S4.case_conj₃ [System.K4 mL] : mL ⊢! (p ⟶ q ⟶ p ⋏ q)ᵍ := by
  simp only [GTranslation.imp_def, GTranslation.and_def];
  exact nec! $ imp_trans! axiomTc_GTranslate! $ axiomK'! $ nec! $ conj₃!

private lemma provable_efq_of_provable_S4.case_disj₃ [System.K4 mL] : mL ⊢! (((p ⟶ r) ⟶ (q ⟶ r) ⟶ (p ⋎ q ⟶ r)))ᵍ := by
  simp only [GTranslation.imp_def, GTranslation.or_def];
  exact nec! $ imp_trans! axiomFour! $ axiomK'! $ nec! $ imp_trans! (axiomK'! $ nec! $ disj₃!) axiomK!;

open provable_efq_of_provable_S4 in
lemma provable_efq_of_provable_S4 (h : 𝐄𝐅𝐐 ⊢! p) : 𝐒𝟒 ⊢! pᵍ := by
  induction h.some with
  | eaxm ih =>
    simp_all only [Set.mem_setOf_eq, Superintuitionistic.axiomEFQ];
    obtain ⟨p, hp⟩ := ih; subst hp;
    exact nec! efq!;
  | mdp hpq hp ihpq ihp =>
    exact axiomT'! $ axiomK''! (by simpa using ihpq ⟨hpq⟩) $ nec! $ ihp ⟨hp⟩;
  | verum => apply verum!;
  | imply₁ => exact case_imply₁;
  | imply₂ => exact case_imply₂;
  | conj₁ => simp only [GTranslation.imp_def, GTranslation.and_def]; exact nec! conj₁!;
  | conj₂ => simp only [GTranslation.imp_def, GTranslation.and_def]; exact nec! conj₂!;
  | conj₃ => exact case_conj₃;
  | disj₁ => simp only [GTranslation.imp_def, GTranslation.or_def]; exact nec! disj₁!;
  | disj₂ => simp only [GTranslation.imp_def, GTranslation.or_def]; exact nec! disj₂!;
  | disj₃ => exact case_disj₃;

open Superintuitionistic.Kripke
open Superintuitionistic.Formula.Kripke

variable [Inhabited (Superintuitionistic.SaturatedConsistentTableau (α := α) 𝐄𝐅𝐐)] --TODO: remove

open Kripke

lemma provable_S4_of_provable_efq : (𝐒𝟒 ⊢! pᵍ) → (𝐄𝐅𝐐 ⊢! p) := by
  contrapose;
  intro h;
  obtain ⟨MI, w, h⟩ := by simpa [
      FrameClass.Intuitionistic,
      ValidOnFrameClass.iff_models, ValidOnFrameClass,
      ValidOnModel.iff_models, ValidOnModel
    ] using not_imp_not.mpr Superintuitionistic.Kripke.complete! h;

  have MTrans := MI.frame_prop.1;
  have MRefl := MI.frame_prop.2;

  let M : Modal.Standard.Kripke.Model _ α := ⟨MI.frame, MI.valuation⟩;
  have h₁ : ∀ q (v : Superintuitionistic.SaturatedConsistentTableau (α := α) 𝐄𝐅𝐐), (MI, v) ⊧ q ↔ (M, v) ⊧ qᵍ := by
    intro q v;
    induction q using Superintuitionistic.Formula.rec' generalizing v with
    | hatom a =>
      constructor;
      . intro _ _ h;
        simp_all only [Satisfies.iff_models, Satisfies, Formula.Kripke.Satisfies];
        exact MI.hereditary h a (by assumption);
      . intro h;
        simpa only [Satisfies.iff_models, Satisfies, Formula.Kripke.Satisfies] using h v (MRefl v);
    | _ => simp_all;
  have : ¬((M, w) ⊧ pᵍ) := (h₁ p w).not.mp h;

  by_contra hC;
  have := by simpa using Modal.Standard.Kripke.sound!_on_frameclass hC;
  have : (M, w) ⊧ pᵍ := this _ M.frame (
      iff_definability_memAxiomSetFrameClass
      (show Kripke.Definability _ (λ F => Reflexive F ∧ Transitive F) by simpa using instGeachDefinability (L := 𝐒𝟒))
      |>.mpr ⟨MRefl, MTrans⟩
    ) M.valuation w;
  contradiction;

/-- a.k.a. _Gödel-McKinsey-Tarski Theorem_ -/
theorem provable_efq_iff_provable_S4 : 𝐄𝐅𝐐 ⊢! p ↔ 𝐒𝟒 ⊢! pᵍ := ⟨provable_efq_of_provable_S4, provable_S4_of_provable_efq⟩
instance : ModalCompanion (α := α) 𝐄𝐅𝐐 𝐒𝟒 := ⟨provable_efq_iff_provable_S4⟩


lemma dp_of_mdp [ModalDisjunctive mL] [ModalCompanion iΛ mL] [S4 mL] : iΛ ⊢! p ⋎ q → iΛ ⊢! p ∨ iΛ ⊢! q := by
    intro hpq;
    have : mL ⊢! □pᵍ ⋎ □qᵍ := disj₃'! (implyOrLeft'! axiomTc_GTranslate!) (implyOrRight'! axiomTc_GTranslate!) (by simpa using ModalCompanion.companion.mp hpq);
    cases ModalDisjunctive.modal_disjunctive this with
    | inl h => left; exact ModalCompanion.companion.mpr h;
    | inr h => right; exact ModalCompanion.companion.mpr h;

theorem disjunctive_of_modalDisjunctive [ModalDisjunctive mL] [ModalCompanion iΛ mL] [S4 mL] : Disjunctive iΛ := ⟨dp_of_mdp (iΛ := iΛ) (mL := mL)⟩

end LO.Modal.Standard

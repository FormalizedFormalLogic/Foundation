import Logic.Modal.Standard.Deduction
import Logic.Propositional.Superintuitionistic.Kripke.Semantics

/-!
  # Maximality of `𝐓𝐫𝐢𝐯` and `𝐕𝐞𝐫`

  `𝐓𝐫𝐢𝐯` and `𝐕𝐞𝐫` are maximal in normal modal logic.
-/

namespace LO.Propositional.Superintuitionistic

def Formula.toModalFormula : Formula α → Modal.Standard.Formula α
  | .atom a => Modal.Standard.Formula.atom a
  | ⊤ => ⊤
  | ⊥ => ⊥
  | ~p => ~(toModalFormula p)
  | p ⟶ q => (toModalFormula p) ⟶ (toModalFormula q)
  | p ⋏ q => (toModalFormula p) ⋏ (toModalFormula q)
  | p ⋎ q => (toModalFormula p) ⋎ (toModalFormula q)
postfix:75 "ᴹ" => Formula.toModalFormula

end LO.Propositional.Superintuitionistic


namespace LO.Modal.Standard

open LO.Propositional

variable {α} [DecidableEq α]

namespace Formula

def toPropFormula (p : Formula α) (_ : p.degree = 0 := by simp_all [Formula.degree, Formula.degree_neg, Formula.degree_imp]) : Superintuitionistic.Formula α :=
  match p with
  | atom a => Superintuitionistic.Formula.atom a
  | natom a => ~Superintuitionistic.Formula.atom a
  | ⊤ => ⊤
  | ⊥ => ⊥
  | p ⋎ q => p.toPropFormula ⋎ q.toPropFormula
  | p ⋏ q => p.toPropFormula ⋏ q.toPropFormula
postfix:75 "ᴾ" => Formula.toPropFormula

namespace toPropFormula

open System
variable {p q : Formula α} (hp : p.degree = 0 := by simpa) (hq : q.degree = 0 := by simpa)

lemma neg_classical : 𝐂𝐥 ⊢! (~p)ᴾ ↔ 𝐂𝐥 ⊢! ~(pᴾ) := by
  induction p using Formula.rec' with
  | hatom => simp only [toPropFormula];
  | hnatom =>
    simp only [toPropFormula];
    exact ⟨dni'!, dne'!⟩;
  | hverum =>
    simp only [toPropFormula];
    exact ⟨efq'!, (by sorry)⟩;
  | hfalsum =>
    simp only [toPropFormula];
    constructor;
    . intro;
      sorry;
    . intro; exact verum!;
  | hand p q ihp ihq =>
    simp only [toPropFormula, Formula.toPropFormula, Formula.degree, Formula.degree_neg, Formula.degree_imp];
    constructor;
    . intro h;
      sorry;
    . sorry;
  | hor p q ihp ihq =>
    simp only [toPropFormula, Formula.toPropFormula, Formula.degree, Formula.degree_neg, Formula.degree_imp];
    constructor;
    . sorry;
    . sorry;
  | _ => simp [degree] at hp;

lemma imp_classical : 𝐂𝐥 ⊢! (pᴾ ⟶ qᴾ) ↔ 𝐂𝐥 ⊢! (toPropFormula (p ⟶ q) (by aesop)) := by
  constructor;
  . intro h;
    simp [Formula.toPropFormula];
    have := lem! (𝓢 := 𝐂𝐥) (p := pᴾ);
    have := or₃'''! (𝓢 := 𝐂𝐥) (p := pᴾ) (q := pᴾ) (r := (~p)ᴾ ⋎ qᴾ);
    sorry;
  . intro h;
    apply or₃'''! ?_ imply₁! h;
    . sorry;

end toPropFormula

def TrivTranslation : Formula α → Formula α
  | atom a => atom a
  | natom a => natom a
  | □p => p.TrivTranslation
  | ◇p => p.TrivTranslation
  | ⊤ => ⊤
  | ⊥ => ⊥
  | p ⋏ q => (p.TrivTranslation) ⋏ (q.TrivTranslation)
  | p ⋎ q => (p.TrivTranslation) ⋎ (q.TrivTranslation)
postfix:75 "ᵀ" => TrivTranslation

namespace TrivTranslation

lemma box_def : (□p)ᵀ = pᵀ := by rfl;

lemma dia_def : (◇p)ᵀ = pᵀ := by rfl;

lemma neg_def : (~p)ᵀ = ~(pᵀ) := by
  induction p using Formula.rec' <;> simp [TrivTranslation, Formula.neg_eq, *];

lemma imp_def : (p ⟶ q)ᵀ = (pᵀ) ⟶ (qᵀ) := by
  simp [TrivTranslation, Formula.imp_eq];
  rw [Formula.neg_eq];
  simp [neg_def];

lemma and_def : (p ⋏ q)ᵀ = (pᵀ) ⋏ (qᵀ) := by
  induction p using Formula.rec' with
  | hand p q ihp ihq => simp [TrivTranslation, Formula.and_eq, ihp, ihq];
  | _ => simp [TrivTranslation, Formula.and_eq];

lemma or_def : (p ⋎ q)ᵀ = (pᵀ) ⋎ (qᵀ) := by
  induction p using Formula.rec' with
  | hor p q ihp ihq => simp [TrivTranslation, Formula.or_eq, ihp, ihq];
  | _ => simp [TrivTranslation, Formula.or_eq];

lemma axiomK : (Axioms.K p q)ᵀ = (pᵀ ⟶ qᵀ) ⟶ pᵀ ⟶ qᵀ := by simp [Axioms.K, imp_def, box_def];

lemma axiomT : (Axioms.T p)ᵀ = pᵀ ⟶ pᵀ := by simp [Axioms.T, imp_def, box_def];

lemma axiomTc : (Axioms.Tc p)ᵀ = pᵀ ⟶ pᵀ := by simp [Axioms.Tc, imp_def, box_def];

@[simp] lemma degree_zero : pᵀ.degree = 0 := by induction p <;> simp [TrivTranslation, degree, *];
@[simp] lemma back : pᵀᴾᴹ = pᵀ := by induction p using rec' <;> simp [Superintuitionistic.Formula.toModalFormula, TrivTranslation, *];

end TrivTranslation


def VerTranslation : Formula α → Formula α
  | atom a => atom a
  | natom a => natom a
  | □_ => ⊤
  | ◇_ => ⊥
  | ⊤ => ⊤
  | ⊥ => ⊥
  | p ⋏ q => (p.VerTranslation) ⋏ (q.VerTranslation)
  | p ⋎ q => (p.VerTranslation) ⋎ (q.VerTranslation)
postfix:75 "ⱽ" => VerTranslation

namespace VerTranslation

lemma box_def : (□p)ⱽ = ⊤ := by rfl;

lemma dia_def : (◇p)ⱽ = ⊥ := by rfl;

lemma neg_def : (~p)ⱽ = ~(pⱽ) := by
  induction p using Formula.rec' <;> simp [VerTranslation, Formula.neg_eq, *];

lemma imp_def : (p ⟶ q)ⱽ = (pⱽ) ⟶ (qⱽ) := by
  simp [VerTranslation, Formula.imp_eq];
  rw [Formula.neg_eq];
  simp [neg_def];

lemma and_def : (p ⋏ q)ⱽ = (pⱽ) ⋏ (qⱽ) := by
  induction p using Formula.rec' with
  | hand p q ihp ihq => simp [VerTranslation, Formula.and_eq, ihp, ihq];
  | _ => simp [VerTranslation, Formula.and_eq];

lemma or_def : (p ⋎ q)ⱽ = (pⱽ) ⋎ (qⱽ) := by
  induction p using Formula.rec' with
  | hor p q ihp ihq => simp [VerTranslation, Formula.or_eq, ihp, ihq];
  | _ => simp [VerTranslation, Formula.or_eq];

lemma axiomK : (Axioms.K p q)ⱽ = ⊤ ⟶ ⊤ ⟶ ⊤ := by simp [Axioms.K, imp_def, box_def];

lemma axiomVer : (Axioms.Ver p)ⱽ = ⊤ := by simp [Axioms.Ver, VerTranslation];

@[simp] lemma degree_zero : pⱽ.degree = 0 := by induction p <;> simp [degree, *];
@[simp] lemma back  : pⱽᴾᴹ = pⱽ := by
  induction p using rec' with
  | hbox _ => simp [VerTranslation, toPropFormula, Superintuitionistic.Formula.toModalFormula];
  | _ => simp [VerTranslation, toPropFormula, Superintuitionistic.Formula.toModalFormula, *];

end VerTranslation

end Formula


open Deduction

variable {p : Formula α}

open System
open Formula

lemma deducible_iff_trivTranslation : 𝐓𝐫𝐢𝐯 ⊢! p ⟷ pᵀ := by
  induction p using Formula.rec' with
  | hbox p ih =>
    simp [TrivTranslation];
    apply iff_intro!;
    . exact imp_trans''! axiomT! (and₁'! ih)
    . exact imp_trans''! (and₂'! ih) axiomTc!
  | hdia p ih =>
    simp [TrivTranslation];
    apply iff_intro!;
    . apply imp_trans''! diaT! (and₁'! ih);
    . apply imp_trans''! (and₂'! ih) diaTc!;
  | hand _ _ ih₁ ih₂ => exact and_replace_iff! ih₁ ih₂;
  | hor _ _ ih₁ ih₂ => exact or_replace_iff! ih₁ ih₂;
  | _ => apply iff_id!

lemma deducible_iff_verTranslation : 𝐕𝐞𝐫 ⊢! p ⟷ pⱽ := by
  induction p using Formula.rec' with
  | hbox =>
    apply iff_intro!;
    . exact imply₁'! verum!
    . exact dhyp! (by simp)
  | hdia =>
    simp [VerTranslation];
    apply iff_intro!;
    . exact bot_of_dia!;
    . exact efq!;
  | hand _ _ ih₁ ih₂ => exact and_replace_iff! ih₁ ih₂;
  | hor _ _ ih₁ ih₂ => exact or_replace_iff! ih₁ ih₂;
  | _ => apply iff_id!

lemma of_classical {mΛ : Modal.Standard.DeductionParameter α} {p : Superintuitionistic.Formula α} : (𝐂𝐥 ⊢! p) → (mΛ ⊢! pᴹ) := by
  intro h;
  induction h.some with
  | eaxm ih =>
    simp_all;
    rcases ih with (⟨_, rfl⟩ | ⟨_, rfl⟩);
    . exact efq!;
    . exact lem!;
  | mdp h₁ h₂ ih₁ ih₂ =>
    dsimp only [Superintuitionistic.Formula.toModalFormula] at ih₁ ih₂;
    exact (ih₁ ⟨h₁⟩) ⨀ (ih₂ ⟨h₂⟩);
  | _ => dsimp [Superintuitionistic.Formula.toModalFormula]; trivial;

lemma iff_Triv_classical : 𝐓𝐫𝐢𝐯 ⊢! p ↔ 𝐂𝐥 ⊢! pᵀᴾ := by
  constructor;
  . intro h;
    induction h using Deduction.inducition_with_necOnly! with
    | hMaxm a =>
      rcases a with (⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩);
      . simp only [TrivTranslation.axiomK];
        apply toPropFormula.imp_classical (by simp) (by simp) |>.mp;
        exact imp_id!;
      . simp only [TrivTranslation.axiomT];
        apply toPropFormula.imp_classical (by simp) (by simp) |>.mp;
        exact imp_id!;
      . simp only [TrivTranslation.axiomTc];
        apply toPropFormula.imp_classical (by simp) (by simp) |>.mp;
        exact imp_id!;
    | hMdp ih₁ ih₂ =>
      simp only [TrivTranslation.imp_def] at ih₁;
      replace ih₁ := toPropFormula.imp_classical (by simp) (by simp) |>.mpr ih₁;
      exact ih₁ ⨀ ih₂;
    | hNec ih => simp_all only [TrivTranslation];
    | _ =>
      sorry;
  . intro h;
    have d₁ : 𝐓𝐫𝐢𝐯 ⊢! pᵀ ⟶ p := and₂'! deducible_iff_trivTranslation;
    have d₂ : 𝐓𝐫𝐢𝐯 ⊢! pᵀ := by simpa only [TrivTranslation.back] using of_classical h;
    exact d₁ ⨀ d₂;

lemma iff_Ver_classical : 𝐕𝐞𝐫 ⊢! p ↔ 𝐂𝐥 ⊢! pⱽᴾ := by
  constructor;
  . intro h;
    induction h using Deduction.inducition_with_necOnly! with
    | hMaxm a =>
      rcases a with (⟨_, _, rfl⟩ | ⟨_, rfl⟩)
      . simp only [VerTranslation.axiomK];
        sorry;
      . simp only [VerTranslation.axiomVer];
        sorry;
    | hMdp ih₁ ih₂ =>
      simp only [VerTranslation.imp_def] at ih₁;
      replace ih₁ := toPropFormula.imp_classical (by simp) (by simp) |>.mpr ih₁;
      exact ih₁ ⨀ ih₂;
    | hNec => dsimp [toPropFormula]; exact verum!;
    | _ =>
      dsimp [VerTranslation, toPropFormula];
      sorry;
  . intro h;
    have d₁ : 𝐕𝐞𝐫 ⊢! pⱽ ⟶ p := and₂'! deducible_iff_verTranslation;
    have d₂ : 𝐕𝐞𝐫 ⊢! pⱽ := by simpa using of_classical h;
    exact d₁ ⨀ d₂;

lemma trivTranslated_of_K4 : 𝐊𝟒 ⊢! p → 𝐂𝐥 ⊢! pᵀᴾ := by
  intro h;
  apply iff_Triv_classical.mp;
  exact System.weakerThan_iff.mp reducible_K4_Triv h;


lemma verTranslated_of_GL : 𝐆𝐋 ⊢! p → 𝐂𝐥 ⊢! pⱽᴾ := by sorry;
/-
lemma verTranslated_of_GL : 𝐆𝐋 ⊢! p → 𝐂𝐥 ⊢! pⱽᴾ := by
  intro h;
  induction h using Deduction.inducition_with_necOnly! with
    | hMaxm a =>
      rcases a with (hK | hVer)
      . obtain ⟨_, _, e⟩ := hK; subst_vars; dsimp only [Axioms.K, VerTranslation, toPropFormula]; apply imply₁!;
      . obtain ⟨_, e⟩ := hVer; subst_vars; dsimp [Axioms.Ver, VerTranslation, toPropFormula]; apply imp_id!;
    | hMdp ih₁ ih₂ =>
      dsimp [VerTranslation, toPropFormula] at ih₁ ih₂;
      exact ih₁ ⨀ ih₂;
    | hNec => dsimp [toPropFormula]; exact verum!;
    | _ =>
      dsimp [VerTranslation, toPropFormula];
      -- trivial;
      sorry;
-/

open Superintuitionistic.Kripke (unprovable_classical_of_exists_ClassicalValuation)

variable [Inhabited α]

example : 𝐓𝐫𝐢𝐯 ⊬! Axioms.L (atom default : Formula α) := by
  apply iff_Triv_classical.not.mpr;
  apply unprovable_classical_of_exists_ClassicalValuation;
  simp [Axioms.L, TrivTranslation, toPropFormula, Superintuitionistic.Formula.Kripke.Satisfies];
  use (λ _ => False);
  trivial;

lemma unprovable_AxiomL_K4 : 𝐊𝟒 ⊬! Axioms.L (atom default : Formula α) := by
  apply not_imp_not.mpr trivTranslated_of_K4;
  apply unprovable_classical_of_exists_ClassicalValuation;
  simp [Axioms.L, TrivTranslation, toPropFormula, Superintuitionistic.Formula.Kripke.Satisfies];
  use (λ _ => False);
  trivial;

theorem strictReducible_K4_GL : (𝐊𝟒 : DeductionParameter α) <ₛ 𝐆𝐋 := by
  dsimp [StrictlyWeakerThan];
  constructor;
  . apply reducible_K4_GL;
  . simp [System.not_weakerThan_iff];
    existsi (Axioms.L (atom default))
    constructor;
    . exact axiomL!;
    . exact unprovable_AxiomL_K4;

lemma unprovable_AxiomT_GL : 𝐆𝐋 ⊬! Axioms.T (atom default : Formula α) := by
  apply not_imp_not.mpr verTranslated_of_GL;
  apply unprovable_classical_of_exists_ClassicalValuation;
  simp [Axioms.T, VerTranslation, toPropFormula, Superintuitionistic.Formula.Kripke.Satisfies];
  use (λ _ => False);
  trivial;


instance instGLConsistencyViaUnprovableAxiomT : System.Consistent (𝐆𝐋 : DeductionParameter α) := by
  apply consistent_iff_exists_unprovable.mpr;
  existsi (Axioms.T (atom default));
  apply unprovable_AxiomT_GL;


theorem notReducible_S4_GL : ¬(𝐒𝟒 : DeductionParameter α) ≤ₛ 𝐆𝐋 := by
  apply System.not_weakerThan_iff.mpr;
  existsi (Axioms.T (atom default));
  constructor;
  . exact axiomT!;
  . exact unprovable_AxiomT_GL;


example : 𝐕𝐞𝐫 ⊬! (~(□⊥) : Formula α) := by
  apply iff_Ver_classical.not.mpr;
  apply unprovable_classical_of_exists_ClassicalValuation;
  dsimp [VerTranslation, toPropFormula, Superintuitionistic.Formula.Kripke.Satisfies];
  use (λ _ => True);
  simp;

end LO.Modal.Standard

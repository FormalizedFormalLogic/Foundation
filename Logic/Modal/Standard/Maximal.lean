import Logic.Modal.Standard.Formula
import Logic.Modal.Standard.Deduction
import Logic.Modal.Standard.HilbertStyle
import Logic.Propositional.Superintuitionistic.Deduction
import Logic.Propositional.Superintuitionistic.Kripke.Soundness

/-!
  # Maximality of `𝐓𝐫𝐢𝐯` and `𝐕𝐞𝐫`

  `𝐓𝐫𝐢𝐯` and `𝐕𝐞𝐫` are maximal in normal modal logic.
-/

namespace LO.Propositional.Superintuitionistic

def Formula.toModalFormula : Formula α → Modal.Standard.Formula α
  | .atom a => Modal.Standard.Formula.atom a
  | ⊤ => ⊤
  | ⊥ => ⊥
  | p ⟶ q => (toModalFormula p) ⟶ (toModalFormula q)
  | p ⋏ q => (toModalFormula p) ⋏ (toModalFormula q)
  | p ⋎ q => (toModalFormula p) ⋎ (toModalFormula q)
postfix:75 "ᴹ" => Formula.toModalFormula

end LO.Propositional.Superintuitionistic


namespace LO.Modal.Standard

open LO.Propositional

variable {α} [DecidableEq α]

namespace Formula

def toPropFormula (p : Formula α) (_ : p.degree = 0 := by simp_all) : Superintuitionistic.Formula α :=
  match p with
  | atom a => Superintuitionistic.Formula.atom a
  | ⊤ => ⊤
  | ⊥ => ⊥
  | p ⋏ q => p.toPropFormula ⋏ q.toPropFormula
  | p ⋎ q => p.toPropFormula ⋎ q.toPropFormula
  | p ⟶ q => p.toPropFormula ⟶ q.toPropFormula
postfix:75 "ᴾ" => Formula.toPropFormula


def TrivTranslation : Formula α → Formula α
  | atom a => atom a
  | box p => p.TrivTranslation
  | ⊤ => ⊤
  | ⊥ => ⊥
  | p ⟶ q => (p.TrivTranslation) ⟶ (q.TrivTranslation)
  | p ⋏ q => (p.TrivTranslation) ⋏ (q.TrivTranslation)
  | p ⋎ q => (p.TrivTranslation) ⋎ (q.TrivTranslation)
postfix:75 "ᵀ" => TrivTranslation

namespace TrivTranslation

@[simp] lemma degree_zero : pᵀ.degree = 0 := by induction p <;> simp [TrivTranslation, degree, *];
@[simp] lemma back : pᵀᴾᴹ = pᵀ := by induction p using rec' <;> simp [Superintuitionistic.Formula.toModalFormula, TrivTranslation, *];

end TrivTranslation


def VerTranslation : Formula α → Formula α
  | atom a => atom a
  | box _ => ⊤
  | ⊤ => ⊤
  | ⊥ => ⊥
  | p ⟶ q => (p.VerTranslation) ⟶ (q.VerTranslation)
  | p ⋏ q => (p.VerTranslation) ⋏ (q.VerTranslation)
  | p ⋎ q => (p.VerTranslation) ⋎ (q.VerTranslation)
postfix:75 "ⱽ" => VerTranslation

namespace VerTranslation

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
  -- have := @Deduction.ofTriv;
  induction p using Formula.rec' with
  | hbox p ih =>
    simp [TrivTranslation];
    apply iff_intro!;
    . exact imp_trans! axiomT! (conj₁'! ih)
    . exact imp_trans! (conj₂'! ih) axiomTc!
  | himp _ _ ih₁ ih₂ => exact imp_replace_iff! ih₁ ih₂;
  | hand _ _ ih₁ ih₂ => exact and_replace_iff! ih₁ ih₂;
  | hor _ _ ih₁ ih₂ => exact or_replace_iff! ih₁ ih₂;
  | _ => apply iff_id!

lemma deducible_iff_verTranslation : 𝐕𝐞𝐫 ⊢! p ⟷ pⱽ := by
  induction p using Formula.rec' with
  | hbox =>
    apply iff_intro!;
    . exact imply₁'! verum!
    . exact dhyp! (by simp)
  | himp _ _ ih₁ ih₂ => exact imp_replace_iff! ih₁ ih₂;
  | hand _ _ ih₁ ih₂ => exact and_replace_iff! ih₁ ih₂;
  | hor _ _ ih₁ ih₂ => exact or_replace_iff! ih₁ ih₂;
  | _ => apply iff_id!

lemma of_classical {m𝓓 : Modal.Standard.DeductionParameter α} {p : Superintuitionistic.Formula α} : (𝐂𝐥 ⊢! p) → (m𝓓 ⊢! pᴹ) := by
  intro h;
  induction h.some with
  | eaxm ih =>
    simp_all;
    rcases ih with (efq | lem);
    . obtain ⟨q, e⟩ := efq; subst_vars; exact efq!;
    . obtain ⟨q, e⟩ := lem; subst_vars; exact lem!;
  | mdp h₁ h₂ ih₁ ih₂ =>
    dsimp only [Superintuitionistic.Formula.toModalFormula] at ih₁ ih₂;
    exact (ih₁ ⟨h₁⟩) ⨀ (ih₂ ⟨h₂⟩);
  | _ =>
    dsimp [Superintuitionistic.Formula.toModalFormula];
    try first
    | apply verum!;
    | apply conj₁!;
    | apply conj₂!;
    | apply conj₃!;
    | apply disj₁!;
    | apply disj₂!;
    | apply disj₃!;
    | apply imply₁!;
    | apply imply₂!;

lemma iff_Triv_classical : 𝐓𝐫𝐢𝐯 ⊢! p ↔ 𝐂𝐥 ⊢! pᵀᴾ := by
  constructor;
  . intro h;
    induction h.some using Deduction.inducition_with_nec with
    | hMaxm a =>
      rcases a with (hK | hT) | hTc;
      . obtain ⟨_, _, e⟩ := hK; subst_vars; dsimp [Axioms.K, TrivTranslation, toPropFormula]; apply imp_id!;
      . obtain ⟨_, e⟩ := hT; subst_vars; dsimp [Axioms.T, TrivTranslation, toPropFormula]; apply imp_id!;
      . obtain ⟨_, e⟩ := hTc; subst_vars; dsimp [Axioms.Tc, TrivTranslation, toPropFormula]; apply imp_id!;
    | hMdp h₁ h₂ ih₁ ih₂ =>
      dsimp [TrivTranslation, toPropFormula] at ih₁ ih₂;
      exact (ih₁ ⟨h₁⟩) ⨀ (ih₂ ⟨h₂⟩);
    | hNec _ ih => exact ih $ axiomT'! h;
    | _ =>
      dsimp [TrivTranslation, toPropFormula];
      try first
      | apply imp_id!;
      | apply verum!;
      | apply conj₁!;
      | apply conj₂!;
      | apply conj₃!;
      | apply disj₁!;
      | apply disj₂!;
      | apply disj₃!;
      | apply imply₁!;
      | apply imply₂!;
      | apply dne!;
  . intro h;
    have d₁ : 𝐓𝐫𝐢𝐯 ⊢! pᵀ ⟶ p := conj₂'! deducible_iff_trivTranslation;
    have d₂ : 𝐓𝐫𝐢𝐯 ⊢! pᵀ := by simpa only [TrivTranslation.back] using of_classical h;
    exact d₁ ⨀ d₂;

lemma iff_Ver_classical : 𝐕𝐞𝐫 ⊢! p ↔ 𝐂𝐥 ⊢! pⱽᴾ := by
  constructor;
  . intro h;
    induction h.some using Deduction.inducition_with_nec with
    | hMaxm a =>
      rcases a with (hK | hVer)
      . obtain ⟨_, _, e⟩ := hK; subst_vars; dsimp only [Axioms.K, VerTranslation, toPropFormula]; apply imply₁!;
      . obtain ⟨_, e⟩ := hVer; subst_vars; dsimp [Axioms.Ver, VerTranslation, toPropFormula]; exact verum!;
    | hMdp h₁ h₂ ih₁ ih₂ =>
      dsimp [VerTranslation, toPropFormula] at ih₁ ih₂;
      exact (ih₁ ⟨h₁⟩) ⨀ (ih₂ ⟨h₂⟩);
    | hNec => dsimp [toPropFormula]; exact verum!;
    | _ =>
      dsimp [VerTranslation, toPropFormula];
      try first
      | apply verum!;
      | apply imply₁!;
      | apply imply₂!;
      | apply conj₁!;
      | apply conj₂!;
      | apply conj₃!;
      | apply disj₁!;
      | apply disj₂!;
      | apply disj₃!;
      | apply dne!;
  . intro h;
    have d₁ : 𝐕𝐞𝐫 ⊢! pⱽ ⟶ p := conj₂'! deducible_iff_verTranslation;
    have d₂ : 𝐕𝐞𝐫 ⊢! pⱽ := by simpa using of_classical h;
    exact d₁ ⨀ d₂;

example : 𝐓𝐫𝐢𝐯 ⊬! Axioms.L p := by
  apply iff_Triv_classical.not.mpr;
  apply not_imp_not.mpr $ Superintuitionistic.Kripke.sound!;
  dsimp [Axioms.L, TrivTranslation, toPropFormula];
  -- TODO: Obviously this is not tautology in classical
  sorry;

example : 𝐕𝐞𝐫 ⊬! (~(□⊥) : Formula α) := by
  apply iff_Ver_classical.not.mpr;
  apply not_imp_not.mpr $ Superintuitionistic.Kripke.sound!;
  dsimp [VerTranslation, toPropFormula];
  -- TODO: Obviously this is not tautology in classical
  sorry;

end LO.Modal.Standard

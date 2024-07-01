import Logic.Modal.Standard.Deduction
import Logic.Propositional.Superintuitionistic.Kripke.Classical

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
  | ~p => ~(toModalFormula p)
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
  | ~p => ~(p.toPropFormula)
  | p ⋏ q => p.toPropFormula ⋏ q.toPropFormula
  | p ⋎ q => p.toPropFormula ⋎ q.toPropFormula
  | p ⟶ q => p.toPropFormula ⟶ q.toPropFormula
postfix:75 "ᴾ" => Formula.toPropFormula


def TrivTranslation : Formula α → Formula α
  | atom a => atom a
  | box p => p.TrivTranslation
  | ⊤ => ⊤
  | ⊥ => ⊥
  | ~p => ~(p.TrivTranslation)
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
  | ~p => ~(p.VerTranslation)
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
  induction p using Formula.rec' with
  | hbox p ih =>
    simp [TrivTranslation];
    apply iff_intro!;
    . exact imp_trans''! axiomT! (and₁'! ih)
    . exact imp_trans''! (and₂'! ih) axiomTc!
  | hneg _ ih => exact neg_replace_iff'! ih;
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
  | hneg _ ih => exact neg_replace_iff'! ih;
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
    . obtain ⟨q, e⟩ := lem; subst_vars; sorry; -- exact lem!;
  | mdp h₁ h₂ ih₁ ih₂ =>
    dsimp only [Superintuitionistic.Formula.toModalFormula] at ih₁ ih₂;
    exact (ih₁ ⟨h₁⟩) ⨀ (ih₂ ⟨h₂⟩);
  | _ => dsimp [Superintuitionistic.Formula.toModalFormula]; trivial;

lemma iff_Triv_classical : 𝐓𝐫𝐢𝐯 ⊢! p ↔ 𝐂𝐥 ⊢! pᵀᴾ := by
  constructor;
  . intro h;
    induction h using Deduction.inducition_with_necOnly! with
    | hMaxm a =>
      rcases a with (hK | hT | hTc);
      . obtain ⟨_, _, e⟩ := hK; subst_vars; dsimp [Axioms.K, TrivTranslation, toPropFormula]; apply imp_id!;
      . obtain ⟨_, e⟩ := hT; subst_vars; dsimp [Axioms.T, TrivTranslation, toPropFormula]; apply imp_id!;
      . obtain ⟨_, e⟩ := hTc; subst_vars; dsimp [Axioms.Tc, TrivTranslation, toPropFormula]; apply imp_id!;
    | hMdp ih₁ ih₂ =>
      dsimp [TrivTranslation, toPropFormula] at ih₁ ih₂;
      exact ih₁ ⨀ ih₂;
    | hNec ih => simp_all only [TrivTranslation];
    | _ => dsimp [TrivTranslation, toPropFormula]; trivial
  . intro h;
    have d₁ : 𝐓𝐫𝐢𝐯 ⊢! pᵀ ⟶ p := and₂'! deducible_iff_trivTranslation;
    have d₂ : 𝐓𝐫𝐢𝐯 ⊢! pᵀ := by simpa only [TrivTranslation.back] using of_classical h;
    exact d₁ ⨀ d₂;

lemma iff_Ver_classical : 𝐕𝐞𝐫 ⊢! p ↔ 𝐂𝐥 ⊢! pⱽᴾ := by
  constructor;
  . intro h;
    induction h using Deduction.inducition_with_necOnly! with
    | hMaxm a =>
      rcases a with (hK | hVer)
      . obtain ⟨_, _, e⟩ := hK; subst_vars; dsimp only [Axioms.K, VerTranslation, toPropFormula]; apply imply₁!;
      . obtain ⟨_, e⟩ := hVer; subst_vars; dsimp [Axioms.Ver, VerTranslation, toPropFormula]; exact verum!;
    | hMdp ih₁ ih₂ =>
      dsimp [VerTranslation, toPropFormula] at ih₁ ih₂;
      exact ih₁ ⨀ ih₂;
    | hNec => dsimp [toPropFormula]; exact verum!;
    | _ => dsimp [VerTranslation, toPropFormula]; trivial;
  . intro h;
    have d₁ : 𝐕𝐞𝐫 ⊢! pⱽ ⟶ p := and₂'! deducible_iff_verTranslation;
    have d₂ : 𝐕𝐞𝐫 ⊢! pⱽ := by simpa using of_classical h;
    exact d₁ ⨀ d₂;

lemma trivTranslated_of_K4 : 𝐊𝟒 ⊢! p → 𝐂𝐥 ⊢! pᵀᴾ := by
  intro h;
  apply iff_Triv_classical.mp;
  exact System.reducible_iff.mp reducible_K4_Triv h;

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
    | _ => dsimp [VerTranslation, toPropFormula]; trivial;

open Superintuitionistic (unprovable_classical_of_exists_ClassicalValuation)

variable [Inhabited α]

example : 𝐓𝐫𝐢𝐯 ⊬! Axioms.L (atom default : Formula α) := by
  apply iff_Triv_classical.not.mpr;
  apply unprovable_classical_of_exists_ClassicalValuation;
  simp [Axioms.L, TrivTranslation, toPropFormula];
  use (λ _ => False);
  trivial;

lemma unprovable_AxiomL_K4 : 𝐊𝟒 ⊬! Axioms.L (atom default : Formula α) := by
  apply not_imp_not.mpr trivTranslated_of_K4;
  apply unprovable_classical_of_exists_ClassicalValuation;
  simp [Axioms.L, TrivTranslation, toPropFormula];
  use (λ _ => False);
  trivial;

theorem strictReducible_K4_GL : (𝐊𝟒 : DeductionParameter α) <ₛ 𝐆𝐋 := by
  dsimp [StrictReducible];
  constructor;
  . apply reducible_K4_GL;
  . simp [System.not_reducible_iff];
    existsi (Axioms.L (atom default))
    constructor;
    . exact axiomL!;
    . exact unprovable_AxiomL_K4;

lemma unprovable_AxiomT_GL : 𝐆𝐋 ⊬! Axioms.T (atom default : Formula α) := by
  apply not_imp_not.mpr verTranslated_of_GL;
  apply unprovable_classical_of_exists_ClassicalValuation;
  simp [Axioms.T, VerTranslation, toPropFormula];
  use (λ _ => False);
  trivial;


instance instGLConsistencyViaUnprovableAxiomT : System.Consistent (𝐆𝐋 : DeductionParameter α) := by
  apply consistent_iff_exists_unprovable.mpr;
  existsi (Axioms.T (atom default));
  apply unprovable_AxiomT_GL;


theorem notReducible_S4_GL : ¬(𝐒𝟒 : DeductionParameter α) ≤ₛ 𝐆𝐋 := by
  apply System.not_reducible_iff.mpr;
  existsi (Axioms.T (atom default));
  constructor;
  . exact axiomT!;
  . exact unprovable_AxiomT_GL;


example : 𝐕𝐞𝐫 ⊬! (~(□⊥) : Formula α) := by
  apply iff_Ver_classical.not.mpr;
  apply unprovable_classical_of_exists_ClassicalValuation;
  dsimp [VerTranslation, toPropFormula];
  use (λ _ => True);
  simp; exact ⟨PUnit.unit, by trivial⟩

end LO.Modal.Standard

import Foundation.IntProp.Kripke.Classical
import Foundation.Modal.IntProp
import Foundation.Modal.Hilbert.Strength

namespace LO.Modal


open IntProp

variable {α} [DecidableEq α]


namespace Formula

def TrivTranslation : Formula α → Formula α
  | atom a => atom a
  | □φ => φ.TrivTranslation
  | ⊥ => ⊥
  | φ ➝ ψ => (φ.TrivTranslation) ➝ (ψ.TrivTranslation)
postfix:75 "ᵀ" => TrivTranslation

namespace TrivTranslation

@[simp] lemma degree_zero : φᵀ.degree = 0 := by induction φ <;> simp [TrivTranslation, degree, *];
@[simp] lemma back : φᵀᴾᴹ = φᵀ := by induction φ using rec' <;> simp [IntProp.Formula.toModalFormula, TrivTranslation, *];

end TrivTranslation


def VerTranslation : Formula α → Formula α
  | atom a => atom a
  | □_ => ⊤
  | ⊥ => ⊥
  | φ ➝ ψ => (φ.VerTranslation) ➝ (ψ.VerTranslation)
postfix:75 "ⱽ" => VerTranslation

namespace VerTranslation

@[simp] lemma degree_zero : φⱽ.degree = 0 := by induction φ <;> simp [degree, *];
@[simp] lemma back  : φⱽᴾᴹ = φⱽ := by
  induction φ using rec' with
  | himp => simp [VerTranslation, toPropFormula, IntProp.Formula.toModalFormula, *];
  | _ => rfl;

end VerTranslation

end Formula


open Hilbert.Deduction

variable {φ : Formula α}

open System
open Formula
open Hilbert

macro_rules | `(tactic| trivial) => `(tactic|
    first
    | apply verum!
    | apply imply₁!
    | apply imply₂!
    | apply elim_contra!
    | apply elim_contra_neg!
    | apply and₁!
    | apply and₂!
    | apply and₃!
    | apply or₁!
    | apply or₂!
    | apply or₃!
    | apply neg_equiv!
    | apply dia_duality!
    | apply imp_id!;
  )

lemma deducible_iff_trivTranslation : (Hilbert.Triv α) ⊢! φ ⭤ φᵀ := by
  induction φ using Formula.rec' with
  | hbox φ ih =>
    simp [TrivTranslation];
    apply iff_intro!;
    . exact imp_trans''! axiomT! (and₁'! ih)
    . exact imp_trans''! (and₂'! ih) axiomTc!
  | himp _ _ ih₁ ih₂ => exact imp_replace_iff! ih₁ ih₂;
  | _ => apply iff_id!

lemma deducible_iff_verTranslation : (Hilbert.Ver α) ⊢! φ ⭤ φⱽ := by
  induction φ using Formula.rec' with
  | hbox =>
    apply iff_intro!;
    . exact imply₁'! verum!
    . exact imply₁'! (by simp)
  | himp _ _ ih₁ ih₂ => exact imp_replace_iff! ih₁ ih₂;
  | _ => apply iff_id!

lemma of_classical {mH : Modal.Hilbert α} {φ : IntProp.Formula α} : ((Hilbert.Cl α) ⊢! φ) → (mH ⊢! φᴹ) := by
  intro h;
  induction h.some with
  | eaxm ih =>
    simp_all;
    rcases ih with (⟨_, rfl⟩ | ⟨_, rfl⟩);
    . exact efq!;
    . exact lem!;
  | mdp h₁ h₂ ih₁ ih₂ =>
    dsimp only [IntProp.Formula.toModalFormula] at ih₁ ih₂;
    exact (ih₁ ⟨h₁⟩) ⨀ (ih₂ ⟨h₂⟩);
  | _ =>
    dsimp [IntProp.Formula.toModalFormula];
    trivial;

lemma iff_Triv_classical : Hilbert.Triv α ⊢! φ ↔ (Hilbert.Cl α) ⊢! φᵀᴾ := by
  constructor;
  . intro h;
    induction h using Deduction.inducition_with_necOnly! with
    | hMaxm a =>
      rcases a with (⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩) <;>
      { dsimp [TrivTranslation]; trivial; };
    | hMdp ih₁ ih₂ =>
      dsimp [TrivTranslation] at ih₁ ih₂;
      exact ih₁ ⨀ ih₂;
    | hNec ih => dsimp [TrivTranslation]; trivial;
    | _ => dsimp [TrivTranslation]; trivial;
  . intro h;
    have d₁ : Hilbert.Triv α ⊢! φᵀ ➝ φ := and₂'! deducible_iff_trivTranslation;
    have d₂ : Hilbert.Triv α ⊢! φᵀ := by simpa only [TrivTranslation.back] using of_classical h;
    exact d₁ ⨀ d₂;

lemma iff_Ver_classical : (Hilbert.Ver α) ⊢! φ ↔ (Hilbert.Cl α) ⊢! φⱽᴾ := by
  constructor;
  . intro h;
    induction h using Deduction.inducition_with_necOnly! with
    | hMaxm a =>
      rcases a with (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;>
      { dsimp [VerTranslation]; trivial; };
    | hMdp ih₁ ih₂ =>
      dsimp [VerTranslation] at ih₁ ih₂;
      exact ih₁ ⨀ ih₂;
    | hNec => dsimp [VerTranslation]; trivial;
    | _ => dsimp [VerTranslation]; trivial;
  . intro h;
    have d₁ : (Hilbert.Ver α) ⊢! φⱽ ➝ φ := and₂'! deducible_iff_verTranslation;
    have d₂ : (Hilbert.Ver α) ⊢! φⱽ := by simpa using of_classical h;
    exact d₁ ⨀ d₂;

lemma trivTranslated_of_K4 : (Hilbert.K4 α) ⊢! φ → (Hilbert.Cl α) ⊢! φᵀᴾ := by
  intro h;
  apply iff_Triv_classical.mp;
  exact System.weakerThan_iff.mp Hilbert.K4_weakerThan_Triv h;


lemma verTranslated_of_GL : (Hilbert.GL α) ⊢! φ → (Hilbert.Cl α) ⊢! φⱽᴾ := by
  intro h;
  induction h using Deduction.inducition_with_necOnly! with
    | hMaxm a =>
      rcases a with (⟨_, _, rfl⟩ | ⟨_, rfl⟩) <;>
      { simp only [VerTranslation]; trivial; };
    | hMdp ih₁ ih₂ =>
      dsimp [VerTranslation] at ih₁ ih₂;
      exact ih₁ ⨀ ih₂;
    | hNec => dsimp [VerTranslation]; exact imp_id!;
    | _ => dsimp [VerTranslation]; trivial;


-- open IntProp.Kripke (unprovable_classical_of_exists_ClassicalValuation)

example (a : ℕ) : Hilbert.Triv ℕ ⊬ Axioms.L (atom a : Formula ℕ) := by
  apply iff_Triv_classical.not.mpr;
  apply IntProp.Hilbert.Cl.unprovable_of_exists_classicalValuation;
  simp [Axioms.L, TrivTranslation, toPropFormula, IntProp.Formula.Kripke.Satisfies];
  use (λ _ => False);
  tauto;

lemma unprovable_AxiomL_K4 {a : ℕ} : Hilbert.K4 ℕ ⊬ Axioms.L (atom a : Formula ℕ) := by
  apply not_imp_not.mpr trivTranslated_of_K4;
  apply IntProp.Hilbert.Cl.unprovable_of_exists_classicalValuation;
  simp [Axioms.L, TrivTranslation, toPropFormula, IntProp.Formula.Kripke.Satisfies];
  use (λ _ => False);
  tauto;

theorem K4_strictReducible_GL : (Hilbert.K4 ℕ) <ₛ (Hilbert.GL ℕ) := by
  dsimp [StrictlyWeakerThan];
  constructor;
  . apply K4_weakerThan_GL;
  . simp [System.not_weakerThan_iff];
    use (Axioms.L (atom 0));
    constructor;
    . exact axiomL!;
    . exact unprovable_AxiomL_K4;

lemma unprovable_AxiomT_GL {a : ℕ} : (Hilbert.GL ℕ) ⊬ Axioms.T (atom a : Formula ℕ) := by
  apply not_imp_not.mpr verTranslated_of_GL;
  apply IntProp.Hilbert.Cl.unprovable_of_exists_classicalValuation;
  simp [Axioms.T, VerTranslation, toPropFormula, IntProp.Formula.Kripke.Satisfies];
  use (λ _ => False);
  tauto;


instance instGLConsistencyViaUnprovableAxiomT : System.Consistent (Hilbert.GL ℕ) := by
  apply consistent_iff_exists_unprovable.mpr;
  use (Axioms.T (atom 0));
  apply unprovable_AxiomT_GL;


theorem not_S4_weakerThan_GL : ¬(Hilbert.S4 ℕ) ≤ₛ (Hilbert.GL ℕ) := by
  apply System.not_weakerThan_iff.mpr;
  existsi (Axioms.T (atom 0));
  constructor;
  . exact axiomT!;
  . exact unprovable_AxiomT_GL;


example : (Hilbert.Ver ℕ) ⊬ (∼(□⊥) : Formula ℕ) := by
  apply iff_Ver_classical.not.mpr;
  apply IntProp.Hilbert.Cl.unprovable_of_exists_classicalValuation;
  dsimp [VerTranslation, toPropFormula, IntProp.Formula.Kripke.Satisfies];
  use (λ _ => True);
  simp;

end LO.Modal

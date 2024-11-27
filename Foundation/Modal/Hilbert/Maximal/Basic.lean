import Foundation.IntProp.Kripke.Classical
import Foundation.Modal.Hilbert.Systems
import Foundation.Modal.IntProp

namespace LO.Modal

open System

open IntProp

open Hilbert
open Hilbert.Deduction
open Formula

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


variable {φ : Formula α}

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


namespace Hilbert

lemma provable_of_classical_provable {mH : Modal.Hilbert α} {φ : IntProp.Formula α} : ((Hilbert.Cl α) ⊢! φ) → (mH ⊢! φᴹ) := by
  intro h;
  induction h.some with
  | eaxm ih =>
    rcases ih with (⟨_, rfl⟩ | ⟨_, rfl⟩);
    . exact efq!;
    . exact lem!;
  | mdp h₁ h₂ ih₁ ih₂ =>
    dsimp only [IntProp.Formula.toModalFormula] at ih₁ ih₂;
    exact (ih₁ ⟨h₁⟩) ⨀ (ih₂ ⟨h₂⟩);
  | _ =>
    dsimp [IntProp.Formula.toModalFormula];
    trivial;

namespace Triv

lemma iff_trivTranslated : (Hilbert.Triv α) ⊢! φ ⭤ φᵀ := by
  induction φ using Formula.rec' with
  | hbox φ ih =>
    apply iff_intro!;
    . exact imp_trans''! axiomT! (and₁'! ih)
    . exact imp_trans''! (and₂'! ih) axiomTc!
  | himp _ _ ih₁ ih₂ => exact imp_replace_iff! ih₁ ih₂;
  | _ => apply iff_id!

protected theorem classical_reducible : Hilbert.Triv α ⊢! φ ↔ (Hilbert.Cl α) ⊢! φᵀᴾ := by
  constructor;
  . intro h;
    induction h using Deduction.inducition_with_necOnly! with
    | hMaxm a =>
      rcases a with (⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩) <;>
      { dsimp [TrivTranslation]; trivial; };
    | hMdp ih₁ ih₂ =>
      dsimp [TrivTranslation] at ih₁ ih₂;
      exact ih₁ ⨀ ih₂;
    | hNec ih => exact ih;
    | _ => dsimp [TrivTranslation]; trivial;
  . intro h;
    have d₁ : Hilbert.Triv α ⊢! φᵀ ➝ φ := and₂'! iff_trivTranslated;
    have d₂ : Hilbert.Triv α ⊢! φᵀ := by simpa only [TrivTranslation.back] using provable_of_classical_provable h;
    exact d₁ ⨀ d₂;

end Triv


namespace Ver

lemma iff_verTranslated : (Hilbert.Ver α) ⊢! φ ⭤ φⱽ := by
  induction φ using Formula.rec' with
  | hbox =>
    apply iff_intro!;
    . exact imply₁'! verum!
    . exact imply₁'! (by simp)
  | himp _ _ ih₁ ih₂ => exact imp_replace_iff! ih₁ ih₂;
  | _ => apply iff_id!

protected lemma classical_reducible : (Hilbert.Ver α) ⊢! φ ↔ (Hilbert.Cl α) ⊢! φⱽᴾ := by
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
    have d₁ : (Hilbert.Ver α) ⊢! φⱽ ➝ φ := and₂'! iff_verTranslated;
    have d₂ : (Hilbert.Ver α) ⊢! φⱽ := by simpa using provable_of_classical_provable h;
    exact d₁ ⨀ d₂;

end Ver


end Hilbert

end LO.Modal

#min_imports

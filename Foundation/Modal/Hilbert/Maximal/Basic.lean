import Foundation.IntProp.Hilbert.WellKnown
import Foundation.Modal.Hilbert.WellKnown
import Foundation.Modal.IntProp

namespace LO.Modal

variable {α} [DecidableEq α]

namespace Formula

def TrivTranslation : Formula α → Formula α
  | .atom a => atom a
  | □φ => φ.TrivTranslation
  | ⊥ => ⊥
  | φ ➝ ψ => (φ.TrivTranslation) ➝ (ψ.TrivTranslation)
postfix:75 "ᵀ" => TrivTranslation

namespace TrivTranslation

@[simp] lemma degree_zero : φᵀ.degree = 0 := by induction φ <;> simp [TrivTranslation, degree, *];

@[simp]
lemma back : φᵀᴾᴹ = φᵀ := by
  induction φ using rec' with
  | himp => simp [TrivTranslation, toPropFormula, IntProp.Formula.toModalFormula, *];
  | hbox => simp [TrivTranslation, *];
  | _ => rfl;

end TrivTranslation


def VerTranslation : Formula α → Formula α
  | atom a => atom a
  | □_ => ⊤
  | ⊥ => ⊥
  | φ ➝ ψ => (φ.VerTranslation) ➝ (ψ.VerTranslation)
postfix:75 "ⱽ" => VerTranslation

namespace VerTranslation

@[simp]
lemma degree_zero : φⱽ.degree = 0 := by
  induction φ using rec' with
  | himp => simp [VerTranslation, degree, *];
  | _ => rfl;

@[simp] lemma back  : φⱽᴾᴹ = φⱽ := by
  induction φ using rec' with
  | himp => simp [VerTranslation, toPropFormula, IntProp.Formula.toModalFormula, *];
  | _ => rfl;

end VerTranslation

end Formula

open Entailment
open Formula (TrivTranslation VerTranslation)

namespace Hilbert

lemma provable_of_classical_provable {mH : Modal.Hilbert ℕ} {φ : IntProp.Formula ℕ} : ((IntProp.Hilbert.Cl) ⊢! φ) → (mH ⊢! φᴹ) := by
  intro h;
  induction h using IntProp.Hilbert.Deduction.rec! with
  | maxm ih =>
    rcases (by simpa using ih) with (⟨_, rfl⟩ | ⟨_, rfl⟩);
    . exact efq!;
    . exact lem!;
  | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
  | _ =>
    dsimp [IntProp.Formula.toModalFormula];
    simp;

namespace Triv


lemma iff_trivTranslated : (Hilbert.Triv) ⊢! φ ⭤ φᵀ := by
  induction φ using Formula.rec' with
  | hbox φ ih =>
    apply iff_intro!;
    . exact imp_trans''! axiomT! (and₁'! ih)
    . exact imp_trans''! (and₂'! ih) axiomTc!
  | himp _ _ ih₁ ih₂ => exact imp_replace_iff! ih₁ ih₂;
  | _ => apply iff_id!

protected theorem classical_reducible : Hilbert.Triv ⊢! φ ↔ (IntProp.Hilbert.Cl) ⊢! φᵀᴾ := by
  constructor;
  . intro h;
    induction h using Deduction.rec! with
    | maxm a =>
      rcases a with ⟨_, (⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩), ⟨_, rfl⟩⟩
      <;> simp [TrivTranslation, Formula.toPropFormula];
    | mdp ih₁ ih₂ =>
      dsimp [TrivTranslation] at ih₁ ih₂;
      exact ih₁ ⨀ ih₂;
    | nec ih => exact ih;
    | _ => simp [TrivTranslation, Formula.toPropFormula];
  . intro h;
    have d₁ : Hilbert.Triv ⊢! φᵀ ➝ φ := and₂'! iff_trivTranslated;
    have d₂ : Hilbert.Triv ⊢! φᵀ := by simpa only [TrivTranslation.back] using provable_of_classical_provable h;
    exact d₁ ⨀ d₂;

end Triv


namespace Ver

lemma iff_verTranslated : (Hilbert.Ver) ⊢! φ ⭤ φⱽ := by
  induction φ using Formula.rec' with
  | hbox =>
    apply iff_intro!;
    . exact imply₁'! verum!
    . exact imply₁'! (by simp)
  | himp _ _ ih₁ ih₂ => exact imp_replace_iff! ih₁ ih₂;
  | _ => apply iff_id!

protected lemma classical_reducible : (Hilbert.Ver) ⊢! φ ↔ (IntProp.Hilbert.Cl) ⊢! φⱽᴾ := by
  constructor;
  . intro h;
    induction h using Deduction.rec! with
    | maxm a =>
      rcases a with ⟨_, (⟨_, _, rfl⟩ | ⟨_, rfl⟩), ⟨_, rfl⟩⟩
      <;> simp [VerTranslation, Formula.toPropFormula];
    | mdp ih₁ ih₂ =>
      dsimp [VerTranslation] at ih₁ ih₂;
      exact ih₁ ⨀ ih₂;
    | _ => simp [VerTranslation, Formula.toPropFormula];
  . intro h;
    have d₁ : Hilbert.Ver ⊢! φⱽ ➝ φ := and₂'! iff_verTranslated;
    have d₂ : Hilbert.Ver ⊢! φⱽ := by simpa using provable_of_classical_provable h;
    exact d₁ ⨀ d₂;

end Ver


end Hilbert

end LO.Modal

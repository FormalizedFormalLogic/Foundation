import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Propositional.ClassicalSemantics.Hilbert
import Foundation.Modal.Hilbert.Normal.Basic

namespace LO.Modal

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

variable {α} [DecidableEq α]

namespace Formula

def trivTranslate : Formula α → Formula α
  | .atom a => atom a
  | □φ => φ.trivTranslate
  | ⊥ => ⊥
  | φ ➝ ψ => (φ.trivTranslate) ➝ (ψ.trivTranslate)
postfix:75 "ᵀ" => trivTranslate

namespace trivTranslate

@[simp]
lemma degree_zero : φᵀ.degree = 0 := by induction φ <;> simp [trivTranslate, degree, *];

@[simp]
lemma toIP : φᵀ.toPropFormula = φᵀ := by
  induction φ using rec' with
  | hbox => simp [trivTranslate, *];
  | himp => simp [trivTranslate, toPropFormula, *];
  | _ => rfl;

end trivTranslate


def verTranslate : Formula α → Formula α
  | atom a => atom a
  | □_ => ⊤
  | ⊥ => ⊥
  | φ ➝ ψ => (φ.verTranslate) ➝ (ψ.verTranslate)
postfix:75 "ⱽ" => verTranslate

namespace verTranslate

@[simp]
lemma degree_zero : φⱽ.degree = 0 := by
  induction φ using rec' with
  | himp => simp [verTranslate, degree, *];
  | _ => rfl;

@[simp]
lemma toIP : φⱽ.toPropFormula = φⱽ := by
  induction φ using rec' with
  | himp => simp [verTranslate, toPropFormula, *];
  | _ => rfl;

end verTranslate

end Formula


open Entailment
open Formula (trivTranslate verTranslate)

lemma Hilbert.provable_of_classical_provable {H : Modal.Hilbert ℕ} {φ : Propositional.Formula ℕ} : Propositional.Hilbert.Cl ⊢! φ → (H.logic ⊢! φ.toModalFormula) := by
  intro h;
  induction h using Propositional.Hilbert.rec! with
  | axm _ h => rcases h with (rfl | rfl) <;> simp;
  | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
  | _ =>
    dsimp [Propositional.Formula.toModalFormula];
    simp;

namespace Logic.Triv

variable {φ : Modal.Formula ℕ}

lemma iff_trivTranslated : Logic.Triv ⊢! φ ⭤ φᵀ := by
  induction φ with
  | hbox φ ih =>
    apply E!_intro;
    . exact C!_trans axiomT! (K!_left ih)
    . exact C!_trans (K!_right ih) axiomTc!
  | himp _ _ ih₁ ih₂ => exact ECC!_of_E!_of_E! ih₁ ih₂;
  | _ => apply E!_id

lemma iff_provable_Cl : Logic.Triv ⊢! φ ↔ Propositional.Hilbert.Cl ⊢! φᵀ.toPropFormula := by
  constructor;
  . intro h;
    induction h with
    | maxm a =>
      rcases a with ⟨_, (⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩), ⟨_, rfl⟩⟩
      <;> simp [trivTranslate, Formula.toPropFormula];
    | mdp ih₁ ih₂ =>
      dsimp [trivTranslate] at ih₁ ih₂;
      exact ih₁ ⨀ ih₂;
    | nec ih => exact ih;
    | _ => simp [trivTranslate, Formula.toPropFormula];
  . intro h;
    have d₁ : Logic.Triv ⊢! φᵀ ➝ φ := K!_right iff_trivTranslated;
    have d₂ : Logic.Triv ⊢! φᵀ := by simpa only [trivTranslate.toIP] using Hilbert.provable_of_classical_provable h;
    exact d₁ ⨀ d₂;

lemma iff_isTautology : Logic.Triv ⊢! φ ↔ φᵀ.toPropFormula.isTautology := by
  apply Iff.trans Triv.iff_provable_Cl;
  apply Propositional.Hilbert.Cl.iff_isTautology_provable.symm;

end Logic.Triv


namespace Logic.Ver

variable {φ : Modal.Formula ℕ}

lemma iff_verTranslated : Logic.Ver ⊢! φ ⭤ φⱽ := by
  induction φ with
  | hbox =>
    apply E!_intro;
    . exact C!_of_conseq! verum!
    . exact C!_of_conseq! (by simp)
  | himp _ _ ih₁ ih₂ => exact ECC!_of_E!_of_E! ih₁ ih₂;
  | _ => apply E!_id

protected lemma iff_provable_Cl : Logic.Ver ⊢! φ ↔ Propositional.Hilbert.Cl ⊢! φⱽ.toPropFormula := by
  constructor;
  . intro h;
    induction h with
    | maxm a =>
      rcases a with ⟨_, (⟨_, _, rfl⟩ | ⟨_, rfl⟩), ⟨_, rfl⟩⟩
      <;> simp [verTranslate, Formula.toPropFormula];
    | mdp ih₁ ih₂ =>
      dsimp [verTranslate] at ih₁ ih₂;
      exact ih₁ ⨀ ih₂;
    | _ => simp [verTranslate, Formula.toPropFormula];
  . intro h;
    have d₁ : Logic.Ver ⊢! φⱽ ➝ φ := K!_right iff_verTranslated;
    have d₂ : Logic.Ver ⊢! φⱽ := by simpa using Hilbert.provable_of_classical_provable h;
    exact d₁ ⨀ d₂;

lemma iff_isTautology : Logic.Ver ⊢! φ ↔ φⱽ.toPropFormula.isTautology := by
  apply Iff.trans Ver.iff_provable_Cl;
  apply Propositional.Hilbert.Cl.iff_isTautology_provable.symm;

end Logic.Ver


end LO.Modal

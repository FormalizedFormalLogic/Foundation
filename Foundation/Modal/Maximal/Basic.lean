import Foundation.Propositional.Hilbert.Basic2
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
  | himp => simp [verTranslate, *];
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

variable {φ : Modal.Formula ℕ}

lemma Hilbert.Normal.provable_of_classical_provable {Ax : Axiom ℕ} {φ : Propositional.Formula ℕ} : Propositional.𝐂𝐥 ⊢! φ → (Hilbert.Normal Ax ⊢! φ.toModalFormula) := by
  intro h;
  induction h using Propositional.Hilbert.rec! with
  | axm _ h => rcases h with (rfl | rfl) <;> simp;
  | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
  | _ => dsimp [Propositional.Formula.toModalFormula]; simp;


namespace Triv

lemma iff_trivTranslated : Modal.Triv ⊢! φ ⭤ φᵀ := by
  induction φ with
  | hbox φ ih =>
    apply E!_intro;
    . exact C!_trans axiomT! (K!_left ih)
    . exact C!_trans (K!_right ih) axiomTc!
  | himp _ _ ih₁ ih₂ => exact ECC!_of_E!_of_E! ih₁ ih₂;
  | _ => apply E!_id

lemma iff_provable_Cl : Modal.Triv ⊢! φ ↔ Propositional.𝐂𝐥 ⊢! φᵀ.toPropFormula := by
  constructor;
  . intro h;
    induction h using Hilbert.Normal.rec! with
    | axm s a =>
      rcases a with (rfl | rfl | rfl) <;> simp [trivTranslate, Formula.toPropFormula];
    | mdp ih₁ ih₂ =>
      dsimp [trivTranslate] at ih₁ ih₂;
      exact ih₁ ⨀ ih₂;
    | nec ih => exact ih;
    | _ => simp [trivTranslate, Formula.toPropFormula];
  . intro h;
    have d₁ : Modal.Triv ⊢! φᵀ ➝ φ := K!_right iff_trivTranslated;
    have d₂ : Modal.Triv ⊢! φᵀ := by simpa only [trivTranslate.toIP] using Hilbert.Normal.provable_of_classical_provable h;
    exact d₁ ⨀ d₂;

lemma iff_isTautology : Modal.Triv ⊢! φ ↔ φᵀ.toPropFormula.isTautology := by
  apply Iff.trans Triv.iff_provable_Cl;
  apply Propositional.𝐂𝐥.iff_isTautology_provable.symm;

end Triv


namespace Ver

lemma iff_verTranslated : Modal.Ver ⊢! φ ⭤ φⱽ := by
  induction φ with
  | hbox =>
    apply E!_intro;
    . exact C!_of_conseq! verum!
    . exact C!_of_conseq! (by simp)
  | himp _ _ ih₁ ih₂ => exact ECC!_of_E!_of_E! ih₁ ih₂;
  | _ => apply E!_id

protected lemma iff_provable_Cl : Modal.Ver ⊢! φ ↔ Propositional.𝐂𝐥 ⊢! φⱽ.toPropFormula := by
  constructor;
  . intro h;
    induction h using Hilbert.Normal.rec! with
    | axm s a =>
      rcases a with (rfl | rfl | rfl) <;> simp [verTranslate, Formula.toPropFormula];
    | mdp ih₁ ih₂ =>
      dsimp [verTranslate] at ih₁ ih₂;
      exact ih₁ ⨀ ih₂;
    | _ => simp [verTranslate, Formula.toPropFormula];
  . intro h;
    have d₁ : Modal.Ver ⊢! φⱽ ➝ φ := K!_right iff_verTranslated;
    have d₂ : Modal.Ver ⊢! φⱽ := by simpa using Hilbert.Normal.provable_of_classical_provable h;
    exact d₁ ⨀ d₂;

lemma iff_isTautology : Modal.Ver ⊢! φ ↔ φⱽ.toPropFormula.isTautology := by
  apply Iff.trans Ver.iff_provable_Cl;
  apply Propositional.𝐂𝐥.iff_isTautology_provable.symm;

end Ver


end LO.Modal

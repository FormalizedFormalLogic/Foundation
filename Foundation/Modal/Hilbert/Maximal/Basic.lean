import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Modal.Hilbert.WellKnown

namespace LO.Modal

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

namespace Hilbert

lemma provable_of_classical_provable {H : Modal.Hilbert ℕ} {φ : Propositional.Formula ℕ} : ((Propositional.Hilbert.Cl) ⊢! φ) → (H ⊢! φ.toModalFormula) := by
  intro h;
  induction h using Propositional.Hilbert.Deduction.rec! with
  | maxm ih =>
    rcases (by simpa using ih) with (⟨_, rfl⟩ | ⟨_, rfl⟩);
    . exact efq!;
    . exact lem!;
  | mdp ihφψ ihφ => exact ihφψ ⨀ ihφ;
  | _ =>
    dsimp [Propositional.Formula.toModalFormula];
    simp;

namespace Triv

lemma iff_trivTranslated : (Hilbert.Triv) ⊢! φ ⭤ φᵀ := by
  induction φ using Formula.rec' with
  | hbox φ ih =>
    apply E!_intro;
    . exact C!_trans axiomT! (K!_left ih)
    . exact C!_trans (K!_right ih) axiomTc!
  | himp _ _ ih₁ ih₂ => exact ECC!_of_E!_of_E! ih₁ ih₂;
  | _ => apply E!_id

protected theorem iff_provable_Cl : Hilbert.Triv ⊢! φ ↔ (Propositional.Hilbert.Cl) ⊢! φᵀ.toPropFormula := by
  constructor;
  . intro h;
    induction h using Deduction.rec! with
    | maxm a =>
      rcases a with ⟨_, (⟨_, _, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩), ⟨_, rfl⟩⟩
      <;> simp [trivTranslate, Formula.toPropFormula];
    | mdp ih₁ ih₂ =>
      dsimp [trivTranslate] at ih₁ ih₂;
      exact ih₁ ⨀ ih₂;
    | nec ih => exact ih;
    | _ => simp [trivTranslate, Formula.toPropFormula];
  . intro h;
    have d₁ : Hilbert.Triv ⊢! φᵀ ➝ φ := K!_right iff_trivTranslated;
    have d₂ : Hilbert.Triv ⊢! φᵀ := by simpa only [trivTranslate.toIP] using provable_of_classical_provable h;
    exact d₁ ⨀ d₂;

end Triv


namespace Ver

lemma iff_verTranslated : (Hilbert.Ver) ⊢! φ ⭤ φⱽ := by
  induction φ using Formula.rec' with
  | hbox =>
    apply E!_intro;
    . exact C!_of_conseq! verum!
    . exact C!_of_conseq! (by simp)
  | himp _ _ ih₁ ih₂ => exact ECC!_of_E!_of_E! ih₁ ih₂;
  | _ => apply E!_id

protected lemma iff_provable_Cl : (Hilbert.Ver) ⊢! φ ↔ (Propositional.Hilbert.Cl) ⊢! φⱽ.toPropFormula := by
  constructor;
  . intro h;
    induction h using Deduction.rec! with
    | maxm a =>
      rcases a with ⟨_, (⟨_, _, rfl⟩ | ⟨_, rfl⟩), ⟨_, rfl⟩⟩
      <;> simp [verTranslate, Formula.toPropFormula];
    | mdp ih₁ ih₂ =>
      dsimp [verTranslate] at ih₁ ih₂;
      exact ih₁ ⨀ ih₂;
    | _ => simp [verTranslate, Formula.toPropFormula];
  . intro h;
    have d₁ : Hilbert.Ver ⊢! φⱽ ➝ φ := K!_right iff_verTranslated;
    have d₂ : Hilbert.Ver ⊢! φⱽ := by simpa using provable_of_classical_provable h;
    exact d₁ ⨀ d₂;

end Ver


end Hilbert

end LO.Modal

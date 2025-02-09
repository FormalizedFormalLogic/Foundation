import Foundation.IntProp.Logic.Basic
import Foundation.Modal.Logic.WellKnown
import Foundation.Modal.Logic.Extension

namespace LO

open System FiniteContext
open Necessitation
open IntProp

def IntProp.Formula.goedelTranslate : IntProp.Formula α → Modal.Formula α
  | .atom a  => □(.atom a)
  | ⊥ => ⊥
  | φ ⋏ ψ => (goedelTranslate φ) ⋏ (goedelTranslate ψ)
  | φ ⋎ ψ => (goedelTranslate φ) ⋎ (goedelTranslate ψ)
  | φ ➝ ψ => □((goedelTranslate φ) ➝ (goedelTranslate ψ))
postfix:90 "ᵍ" => IntProp.Formula.goedelTranslate

class Modal.ModalCompanion (IL : IntProp.Logic) (ML : Modal.Logic) where
  companion : ∀ {φ}, φ ∈ IL ↔ φᵍ ∈ ML

lemma Modal.instModalCompanion (h₁ : ∀ {φ}, φ ∈ IL → φᵍ ∈ ML) (h₂ : ∀ {φ}, φᵍ ∈ ML → φ ∈ IL) : Modal.ModalCompanion IL ML := ⟨λ {_} => ⟨h₁, h₂⟩⟩


def IntProp.Logic.minimamMC (IL : IntProp.Logic) : Modal.Logic := Modal.Logic.sumNormal Modal.Logic.S4 { φᵍ | φ ∈ IL }

def IntProp.Logic.maximalMC (IL : IntProp.Logic) : Modal.Logic := Modal.Logic.addNormal IL.minimamMC (Axioms.Grz (.atom 0))

/-
lemma dp_of_mdp [ModalDisjunctive mH] [ModalCompanion iH mH] [System.S4 mH] : iH ⊢! φ ⋎ ψ → iH ⊢! φ ∨ iH ⊢! ψ := by
    intro hpq;
    have : mH ⊢! □φᵍ ⋎ □ψᵍ := or₃'''! (imply_left_or'! axiomTc_GTranslate!) (imply_right_or'! axiomTc_GTranslate!) (by simpa using ModalCompanion.companion.mp hpq);
    cases ModalDisjunctive.modal_disjunctive this with
    | inl h => left; exact ModalCompanion.companion.mpr h;
    | inr h => right; exact ModalCompanion.companion.mpr h;

theorem disjunctive_of_modalDisjunctive [ModalDisjunctive mH] [ModalCompanion iH mH] [System.S4 mH] : Disjunctive iH := ⟨dp_of_mdp (iH := iH) (mH := mH)⟩
-/

end LO

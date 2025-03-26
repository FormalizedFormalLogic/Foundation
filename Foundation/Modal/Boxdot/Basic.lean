import Foundation.Modal.Logic.Basic

namespace LO.Modal

open Entailment
open Formula
open Hilbert.Deduction

variable [DecidableEq α]
variable {φ : Formula α}

def Formula.BoxdotTranslation : Formula α → Formula α
  | atom a => .atom a
  | ⊥ => ⊥
  | φ ➝ ψ => (BoxdotTranslation φ) ➝ (BoxdotTranslation ψ)
  | □φ => ⊡(BoxdotTranslation φ)
postfix:90 "ᵇ" => Formula.BoxdotTranslation

class BoxdotProperty (L₁ L₂ : Logic) where
  bdp {φ} : φᵇ ∈ L₁ ↔ φ ∈ L₂


theorem Hilbert.boxdotTranslated_of_dominate {H₁ H₂ : Hilbert α} [Entailment.Modal.K H₂]
  (h : ∀ φ ∈ H₁.axiomInstances, H₂ ⊢! φᵇ) : H₁ ⊢! φ → H₂ ⊢! φᵇ := by
  intro d;
  induction d using Hilbert.Deduction.rec! with
  | maxm hs => exact h _ hs;
  | mdp ihpq ihp => exact ihpq ⨀ ihp;
  | nec ihp => exact boxdot_nec! $ ihp;
  | imply₂ => exact imply₂!;
  | imply₁ => exact imply₁!;
  | ec => exact elim_contra!;


end LO.Modal

import Foundation.Modal.Hilbert.Basic

namespace LO.Modal

open System
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

class BoxdotProperty (H₁ H₂ : Hilbert α) where
  bdp {φ} : H₁ ⊢! φᵇ ↔ H₂ ⊢! φ

theorem boxdotTranslated {H₁ H₂ : Hilbert α}
  [System.K H₂]
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

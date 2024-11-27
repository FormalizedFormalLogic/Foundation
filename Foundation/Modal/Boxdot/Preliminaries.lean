import Foundation.Modal.Hilbert.Preliminaries

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

theorem boxdotTranslated
  {H₁ H₂ : Hilbert α} [H₁.IsNormal] [H₂.IsNormal]
  (h : ∀ φ ∈ H₁.axioms, H₂ ⊢! φᵇ) : H₁ ⊢! φ → H₂ ⊢! φᵇ := by
  intro d;
  induction d using inducition_with_necOnly! with
  | hMaxm hs => exact h _ hs;
  | hNec ihp => exact boxdot_nec! $ ihp;
  | hMdp ihpq ihp => exact ihpq ⨀ ihp;
  | hElimContra => exact elim_contra!;
  | hImply₂ => exact imply₂!;
  | hImply₁ => exact imply₁!;

end LO.Modal

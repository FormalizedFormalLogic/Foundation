/-
  D. de Jongh, M. Fetemeh Shirmohammadzadeh, "Below Gödel-Dummett"
-/

import Foundation.Propositional.Kripke2.Basic
import Foundation.Propositional.Entailment.LC
import Foundation.Vorspiel.HRel.Convergent
import Foundation.Vorspiel.HRel.Euclidean
import Foundation.Vorspiel.HRel.Coreflexive
import Foundation.Vorspiel.HRel.Connected

namespace LO.Propositional

namespace Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

protected alias PCon₁ := LO.Axioms.Dummett

protected abbrev PCon₂ := (φ ➝ ψ) ➝ ((φ ➝ ψ) ➝ φ)

protected abbrev PCon₃ := (φ ➝ ψ) ➝ ((φ ➝ ψ) ➝ ψ)

protected abbrev PCon₄ := (φ ➝ ψ ⋎ χ) ➝ (φ ➝ ψ) ⋎ (φ ➝ χ)

protected abbrev PCon₅ := (φ ⋏ ψ ⋎ χ) ➝ (φ ➝ χ) ⋎ (φ ➝ ψ)

protected abbrev PCon₆ := ((φ ➝ ψ) ➝ ψ) ⋏ ((ψ ➝ φ) ➝ φ) ➝ (φ ⋎ ψ)

end Axioms


open Kripke2
open Formula.Kripke2

namespace Kripke2

variable {F : Kripke2.Frame} {φ ψ : Formula ℕ}

namespace Frame

protected abbrev IsPiecewiseConnected (F : Kripke2.Frame) := _root_.IsPiecewiseConnected F.Rel
@[grind →] lemma p_connected  [F.IsPiecewiseConnected] : ∀ {x y z : F}, x ≺ y → x ≺ z → y ≺ z ∨ y = z ∨ z ≺ y := by apply IsPiecewiseConnected.p_connected
@[grind →] lemma p_connected' [F.IsPiecewiseConnected] : ∀ {x y z : F}, x ≺ y → x ≺ z → y ≠ z → y ≺ z ∨ z ≺ y := by apply IsPiecewiseConnected.p_connected'

end Frame

-- TODO: need formula level hereditary
@[simp high, grind .]
lemma valid_axiomSym_of_isSymmetric [F.IsPiecewiseConnected] : F ⊧ Axioms.PCon₁ φ ψ := by
  intro V x;
  by_contra hC;
  rcases Satisfies.not_def_or.mp hC with ⟨h₁, h₂⟩; clear hC;
  obtain ⟨y, Rxy, hy₁, hy₂⟩ := Satisfies.not_def_imp.mp h₁; clear h₁;
  obtain ⟨z, Rxz, hz₁, hz₂⟩ := Satisfies.not_def_imp.mp h₂; clear h₂;
  rcases F.p_connected Rxy Rxz with Ryz | rfl | Rzy;
  . sorry;
  . tauto;
  . sorry;

end Kripke2

end LO.Propositional

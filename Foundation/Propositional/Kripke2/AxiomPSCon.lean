module

public import Foundation.Propositional.Kripke2.Basic

@[expose] public section

namespace LO.Propositional

namespace Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ ξ : F)

protected abbrev PSCon := ((χ ⋏ (φ ➝ ψ)) ➝ ξ) ⋎ ((φ ⋏ (χ ➝ ξ)) ➝ ψ)

end Axioms

open Kripke2
open Formula.Kripke2

namespace Kripke2

variable {F : Kripke2.Frame} {φ ψ χ ξ : Formula ℕ}

namespace Frame

protected abbrev IsPiecewiseStronglyConnected (F : Kripke2.Frame) := _root_.IsPiecewiseStronglyConnected F.Rel
@[grind →] lemma ps_connected [F.IsPiecewiseStronglyConnected] : ∀ {x y z : F}, x ≺ y → x ≺ z → y ≺ z ∨ z ≺ y := by apply IsPiecewiseStronglyConnected.ps_connected

end Frame

@[simp high, grind .]
lemma valid_axiomPSCon_of_IsPiecewiseStronglyConnected [F.IsPiecewiseStronglyConnected] : F ⊧ Axioms.PSCon φ ψ χ ξ := by
  intro V x;
  by_contra hC;
  rcases Satisfies.not_def_or.mp hC with ⟨h₁, h₂⟩;
  obtain ⟨y, Rxy, ⟨hy₁, hy₂⟩, hy₃⟩ := Satisfies.not_def_imp.mp h₁;
  obtain ⟨z, Rxz, ⟨hz₁, hz₂⟩, hz₃⟩ := Satisfies.not_def_imp.mp h₂;
  rcases F.ps_connected Rxy Rxz with Ryz | Rzy;
  . apply hz₃ $ hy₂ Ryz hz₁;
  . apply hy₃ $ hz₂ Rzy hy₁;

/-
lemma isPiecewiseStronglyConnected_of_valid_axiomPSCon (h : F ⊧ Axioms.PSCon #0 #1 #2 #3) : F.IsPiecewiseStronglyConnected := by
  constructor;
  intro x y z Rxy Rxz;
  rcases @h (λ a w => match a with | 0 => z = w | 1 => w ≺ y | 2 => y = w | 3 => w ≺ z | _ => False) x with h | h;
  . left;
    apply h Rxy;
    constructor;
    . tauto;
    . simp [Satisfies];
      sorry;
  . right;
    apply h Rxz;
    constructor;
    . tauto;
    . rintro w Rzw rfl;
      simp [Satisfies];
      sorry;
-/

end Kripke2

end LO.Propositional
end

/-
  Naming of axioms are refered from:
  - T. Kurahashi, Y. Okawa, "Modal completeness of sublogics of the  interpretability logic IL"
-/
import Foundation.InterpretabilityLogic.LogicSymbol

namespace LO.InterpretabilityLogic.Axioms

variable {F : Type*} [InterpretabilityLogicalConnective F]
variable (φ ψ χ : F)

protected abbrev J1 := □(φ ➝ ψ) ➝ (φ ▷ ψ)

protected abbrev J1' := (φ ▷ φ)


protected abbrev J2 := (φ ▷ ψ) ➝ (ψ ▷ χ) ➝ (φ ▷ χ)

protected abbrev J2Plus := (φ ▷ (ψ ⋎ χ)) ➝ (ψ ▷ χ) ➝ (φ ▷ χ)

protected abbrev J2Plus' := (φ ▷ ψ) ➝ ((ψ ⋏ ∼χ) ▷ χ) ➝ (φ ▷ χ)


protected abbrev J3 := (φ ▷ χ) ➝ (ψ ▷ χ) ➝ ((φ ⋎ ψ) ▷ χ)


protected abbrev J4 := (φ ▷ ψ) ➝ (◇φ ➝ ◇ψ)

protected abbrev J4' := (φ ▷ ψ) ➝ ((ψ ▷ ⊥) ➝ (φ ▷ ⊥))

protected abbrev J4Plus := □(φ ➝ ψ) ➝ (χ ▷ φ ➝ χ ▷ ψ)

protected abbrev J4Plus' := □φ ➝ (χ ▷ (φ ➝ ψ) ➝ χ ▷ ψ)

protected abbrev J4Plus'' := □φ ➝ (χ ▷ ψ ➝ χ ▷ (φ ⋏ ψ))


protected abbrev J5 := ◇φ ▷ φ

protected abbrev J6 := □φ ⭤ (∼φ ▷ ⊥)

/-- Persistency Principle -/
protected abbrev P := (φ ▷ ψ) ➝ □(φ ▷ ψ)

/-- Montagna's Principle -/
protected abbrev M := (φ ▷ ψ) ➝ ((φ ⋏ □χ) ▷ (ψ ⋏ □χ))

end LO.InterpretabilityLogic.Axioms

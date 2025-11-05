/-
  Naming of axioms are refered from:

  - T. Kurahashi, Y. Okawa, 2021, "Modal completeness of sublogics of the  interpretability logic IL"
  - A. Visser, 1988, "Preliminary Notes on Interpretability Logic"
  - V. Švejdar, 1991, "Some independence results in interpretability logic"
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

/--
  - Visser 1988, `K2`
-/
protected abbrev J4' := (φ ▷ ψ) ➝ ((ψ ▷ ⊥) ➝ (φ ▷ ⊥))

/--
  - Visser 1988, `K1`
-/
protected abbrev J4Plus := □(φ ➝ ψ) ➝ (χ ▷ φ ➝ χ ▷ ψ)

protected abbrev J4Plus' := □φ ➝ (χ ▷ (φ ➝ ψ) ➝ χ ▷ ψ)

protected abbrev J4Plus'' := □φ ➝ (χ ▷ ψ ➝ χ ▷ (φ ⋏ ψ))


protected abbrev J5 := ◇φ ▷ φ

protected abbrev J6 := □φ ⭤ (∼φ ▷ ⊥)

/-- Persistency Principle -/
protected abbrev P := (φ ▷ ψ) ➝ □(φ ▷ ψ)

/-- Montagna's Principle -/
protected abbrev M := (φ ▷ ψ) ➝ ((φ ⋏ □χ) ▷ (ψ ⋏ □χ))

/--
  - Visser 1988, `K12`
  - Švejdar 1991, `KM1`
-/
protected abbrev KM1 := (φ ▷ ◇ψ) ➝ □(φ ➝ ◇ψ)

end LO.InterpretabilityLogic.Axioms

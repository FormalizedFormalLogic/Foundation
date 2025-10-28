import Foundation.InterpretabilityLogic.LogicSymbol

namespace LO.InterpretabilityLogic.Axioms

variable {F : Type*} [InterpretabilityLogicalConnective F]
variable (φ ψ χ : F)

protected abbrev J1 := □(φ ➝ ψ) ➝ (φ ▷ ψ)

protected abbrev J2 := (φ ▷ ψ) ➝ (ψ ➝ χ) ➝ (φ ▷ χ)

protected abbrev J3 := (φ ▷ χ) ➝ (ψ ▷ χ) ➝ ((φ ⋎ ψ) ▷ χ)

protected abbrev J4 := (φ ▷ ψ) ➝ (◇φ ➝ ◇ψ)

protected abbrev J5 := ◇φ ▷ φ

end LO.InterpretabilityLogic.Axioms

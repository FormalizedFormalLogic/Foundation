import Foundation.Logic.Entailment

namespace LO.Axioms

section

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

protected abbrev WeakLEM := ∼φ ⋎ ∼∼φ

protected abbrev Dummett := (φ ➝ ψ) ⋎ (ψ ➝ φ)

protected abbrev Peirce := ((φ ➝ ψ) ➝ φ) ➝ φ

protected abbrev KrieselPutnam := (∼φ ➝ ψ ⋎ χ) ➝ (∼φ ➝ ψ) ⋎ (∼φ ➝ χ)

protected abbrev Scott := ((∼∼φ ➝ φ) ➝ (φ ⋎ ∼φ)) ➝ ∼φ ⋎ ∼∼φ

end

end LO.Axioms

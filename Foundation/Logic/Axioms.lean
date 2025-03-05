import Foundation.Logic.Entailment

namespace LO.Axioms

section

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

protected abbrev Verum : F := ⊤

protected abbrev Imply₁ := φ ➝ ψ ➝ φ

protected abbrev Imply₂ := (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ

protected abbrev ElimContra := (∼ψ ➝ ∼φ) ➝ (φ ➝ ψ)

protected abbrev AndElim₁ := φ ⋏ ψ ➝ φ

protected abbrev AndElim₂ := φ ⋏ ψ ➝ ψ

protected abbrev AndInst := φ ➝ ψ ➝ φ ⋏ ψ

protected abbrev OrInst₁ := φ ➝ φ ⋎ ψ

protected abbrev OrInst₂ := ψ ➝ φ ⋎ ψ

protected abbrev OrElim := (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ)

protected abbrev NegEquiv := ∼φ ⭤ (φ ➝ ⊥)

protected abbrev EFQ := ⊥ ➝ φ

protected abbrev LEM := φ ⋎ ∼φ

protected abbrev WeakLEM := ∼φ ⋎ ∼∼φ

protected abbrev Dummett := (φ ➝ ψ) ⋎ (ψ ➝ φ)

protected abbrev DNE := ∼∼φ ➝ φ

protected abbrev Peirce := ((φ ➝ ψ) ➝ φ) ➝ φ

end

end LO.Axioms

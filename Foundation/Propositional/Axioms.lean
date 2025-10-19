import Foundation.Logic.Entailment

namespace LO.Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)


protected abbrev Verum : F := ⊤

protected abbrev ImplyK := φ ➝ ψ ➝ φ
@[deprecated] protected alias Imply₁ := Axioms.ImplyK

protected abbrev ImplyS := (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ
@[deprecated] protected alias Imply₂ := Axioms.ImplyS

protected abbrev AndElim₁ := φ ⋏ ψ ➝ φ

protected abbrev AndElim₂ := φ ⋏ ψ ➝ ψ

protected abbrev AndInst := φ ➝ ψ ➝ φ ⋏ ψ

protected abbrev OrInst₁ := φ ➝ φ ⋎ ψ

protected abbrev OrInst₂ := ψ ➝ φ ⋎ ψ

protected abbrev OrElim := (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ)

protected abbrev NegEquiv := ∼φ ⭤ (φ ➝ ⊥)


protected abbrev ElimContra := (∼ψ ➝ ∼φ) ➝ (φ ➝ ψ)


protected abbrev EFQ := ⊥ ➝ φ

protected abbrev LEM := φ ⋎ ∼φ

protected abbrev DNE := ∼∼φ ➝ φ

protected abbrev WeakLEM := ∼φ ⋎ ∼∼φ

protected abbrev Dummett := (φ ➝ ψ) ⋎ (ψ ➝ φ)

protected abbrev Peirce := ((φ ➝ ψ) ➝ φ) ➝ φ

protected abbrev KrieselPutnam := (∼φ ➝ ψ ⋎ χ) ➝ (∼φ ➝ ψ) ⋎ (∼φ ➝ χ)

protected abbrev Scott := ((∼∼φ ➝ φ) ➝ (φ ⋎ ∼φ)) ➝ ∼φ ⋎ ∼∼φ

end LO.Axioms

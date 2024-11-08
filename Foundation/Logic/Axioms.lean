import Foundation.Logic.System
import Foundation.Logic.Init

namespace LO.Axioms

section

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

protected abbrev Verum : F := ⊤
abbrev Verum.set : Set F := { Axioms.Verum }

protected abbrev Imply₁ := φ ➝ ψ ➝ φ
abbrev Imply₁.set : Set F := { Axioms.Imply₁ φ ψ | (φ) (ψ) }

protected abbrev Imply₂ := (φ ➝ ψ ➝ χ) ➝ (φ ➝ ψ) ➝ φ ➝ χ
abbrev Imply₂.set : Set F := { Axioms.Imply₂ φ ψ χ | (φ) (ψ) (χ) }

protected abbrev ElimContra := (∼ψ ➝ ∼φ) ➝ (φ ➝ ψ)
abbrev ElimContra.set : Set F := { Axioms.ElimContra φ ψ | (φ) (ψ) }

protected abbrev AndElim₁ := φ ⋏ ψ ➝ φ
abbrev AndElim₁.set : Set F := { Axioms.AndElim₁ φ ψ | (φ) (ψ) }

protected abbrev AndElim₂ := φ ⋏ ψ ➝ ψ
abbrev AndElim₂.set : Set F := { Axioms.AndElim₂ φ ψ | (φ) (ψ) }

protected abbrev AndInst := φ ➝ ψ ➝ φ ⋏ ψ
abbrev AndInst.set : Set F := { Axioms.AndInst φ ψ | (φ) (ψ) }

protected abbrev OrInst₁ := φ ➝ φ ⋎ ψ
abbrev OrInst₁.set : Set F := { Axioms.OrInst₁ φ ψ | (φ) (ψ) }

protected abbrev OrInst₂ := ψ ➝ φ ⋎ ψ
abbrev OrInst₂.set : Set F := { Axioms.OrInst₂ φ ψ | (φ) (ψ) }

protected abbrev OrElim := (φ ➝ χ) ➝ (ψ ➝ χ) ➝ (φ ⋎ ψ ➝ χ)
abbrev OrElim.set : Set F := { Axioms.OrElim φ ψ χ | (φ) (ψ) (χ) }

protected abbrev NegEquiv := ∼φ ⭤ (φ ➝ ⊥)
abbrev NegEquiv.set : Set F := { Axioms.NegEquiv φ | (φ) }

protected abbrev EFQ := ⊥ ➝ φ
abbrev EFQ.set : Set F := { Axioms.EFQ φ | (φ) }
notation "𝗘𝗙𝗤" => EFQ.set

protected abbrev LEM := φ ⋎ ∼φ
abbrev LEM.set : Set F := { Axioms.LEM φ | (φ) }
notation "𝗟𝗘𝗠" => LEM.set

protected abbrev WeakLEM := ∼φ ⋎ ∼∼φ
abbrev WeakLEM.set : Set F := { Axioms.WeakLEM φ | (φ) }
notation "𝗪𝗟𝗘𝗠" => WeakLEM.set

protected abbrev Dummett := (φ ➝ ψ) ⋎ (ψ ➝ φ)
abbrev Dummett.set : Set F := { Axioms.Dummett φ ψ | (φ) (ψ) }
notation "𝗗𝘂𝗺" => Dummett.set

protected abbrev DNE := ∼∼φ ➝ φ
abbrev DNE.set : Set F := { Axioms.DNE φ | (φ) }
notation "𝗗𝗡𝗘" => DNE.set

protected abbrev Peirce := ((φ ➝ ψ) ➝ φ) ➝ φ
abbrev Peirce.set : Set F := { Axioms.Peirce φ ψ | (φ) (ψ) }
notation "𝗣𝗲" => Peirce.set

end

end LO.Axioms

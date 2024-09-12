import Logic.Logic.System
import Logic.Logic.Init

namespace LO.Axioms

section

variable {F : Type*} [LogicalConnective F]
variable (p q r : F)

protected abbrev Verum : F := ⊤
abbrev Verum.set : Set F := { Axioms.Verum }

protected abbrev Imply₁ := p ➝ q ➝ p
abbrev Imply₁.set : Set F := { Axioms.Imply₁ p q | (p) (q) }

protected abbrev Imply₂ := (p ➝ q ➝ r) ➝ (p ➝ q) ➝ p ➝ r
abbrev Imply₂.set : Set F := { Axioms.Imply₂ p q r | (p) (q) (r) }

protected abbrev ElimContra := (∼q ➝ ∼p) ➝ (p ➝ q)
abbrev ElimContra.set : Set F := { Axioms.ElimContra p q | (p) (q) }

protected abbrev AndElim₁ := p ⋏ q ➝ p
abbrev AndElim₁.set : Set F := { Axioms.AndElim₁ p q | (p) (q) }

protected abbrev AndElim₂ := p ⋏ q ➝ q
abbrev AndElim₂.set : Set F := { Axioms.AndElim₂ p q | (p) (q) }

protected abbrev AndInst := p ➝ q ➝ p ⋏ q
abbrev AndInst.set : Set F := { Axioms.AndInst p q | (p) (q) }

protected abbrev OrInst₁ := p ➝ p ⋎ q
abbrev OrInst₁.set : Set F := { Axioms.OrInst₁ p q | (p) (q) }

protected abbrev OrInst₂ := q ➝ p ⋎ q
abbrev OrInst₂.set : Set F := { Axioms.OrInst₂ p q | (p) (q) }

protected abbrev OrElim := (p ➝ r) ➝ (q ➝ r) ➝ (p ⋎ q ➝ r)
abbrev OrElim.set : Set F := { Axioms.OrElim p q r | (p) (q) (r) }

protected abbrev NegEquiv := ∼p ⭤ (p ➝ ⊥)
abbrev NegEquiv.set : Set F := { Axioms.NegEquiv p | (p) }

protected abbrev EFQ := ⊥ ➝ p
abbrev EFQ.set : Set F := { Axioms.EFQ p | (p) }
notation "𝗘𝗙𝗤" => EFQ.set

protected abbrev LEM := p ⋎ ∼p
abbrev LEM.set : Set F := { Axioms.LEM p | (p) }
notation "𝗟𝗘𝗠" => LEM.set

protected abbrev WeakLEM := ∼p ⋎ ∼∼p
abbrev WeakLEM.set : Set F := { Axioms.WeakLEM p | (p) }
notation "𝗪𝗟𝗘𝗠" => WeakLEM.set

protected abbrev GD := (p ➝ q) ⋎ (q ➝ p)
abbrev GD.set : Set F := { Axioms.GD p q | (p) (q) }
notation "𝗗𝘂𝗺" => GD.set

protected abbrev DNE := ∼∼p ➝ p
abbrev DNE.set : Set F := { Axioms.DNE p | (p) }
notation "𝗗𝗡𝗘" => DNE.set

protected abbrev Peirce := ((p ➝ q) ➝ p) ➝ p
abbrev Peirce.set : Set F := { Axioms.Peirce p q | (p) (q) }
notation "𝗣𝗲" => Peirce.set

end

end LO.Axioms

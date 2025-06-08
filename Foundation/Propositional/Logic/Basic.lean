import Foundation.Propositional.Formula

namespace LO.Propositional

abbrev Logic := Set (Propositional.Formula ℕ)

namespace Logic

class Consistent (L : Logic) : Prop where
  consis : L ≠ Set.univ
attribute [simp] Consistent.consis

protected class Disjunctive (L : Logic) where
  disjunctive {φ ψ} : φ ⋎ ψ ∈ L → φ ∈ L ∨ ψ ∈ L

end Logic


protected abbrev Logic.Empty : Logic := ∅

protected abbrev Logic.Univ : Logic := Set.univ

end LO.Propositional

import Foundation.Modal.Formula

namespace LO.Modal

abbrev Logic := Set (Modal.Formula ℕ)

namespace Logic

class Consistent (L : Logic) : Prop where
  consis : L ≠ Set.univ
attribute [simp] Consistent.consis


protected class Unnecessitation (L : Logic) where
  unnec_closed {φ} : □φ ∈ L → φ ∈ L

protected class ModalDisjunctive (L : Logic) where
  modal_disjunctive_closed {φ ψ} : □φ ⋎ □ψ ∈ L → φ ∈ L ∨ ψ ∈ L

end Logic


protected abbrev Logic.Empty : Logic := ∅

protected abbrev Logic.Univ : Logic := Set.univ

end LO.Modal

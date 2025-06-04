import Foundation.Modal.Formula

namespace LO.Modal

abbrev Logic := Set (Modal.Formula ℕ)



namespace Logic

variable {L₁ L₂ L₃ : Logic}

class Sublogic (L₁ L₂ : Logic) where
  subset : L₁ ⊆ L₂


class ProperSublogic (L₁ L₂ : Logic) : Prop where
  ssubset : L₁ ⊂ L₂

instance [ProperSublogic L₁ L₂] : Sublogic L₁ L₂ where
  subset := ProperSublogic.ssubset.subset

def ProperSublogic.trans (L₁ L₂ L₃ : Logic) [ProperSublogic L₁ L₂] [ProperSublogic L₂ L₃] : ProperSublogic L₁ L₃ where
  ssubset := by
    trans L₂;
    . exact ProperSublogic.ssubset;
    . exact ProperSublogic.ssubset;


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

instance {L : Logic} [L.Consistent] : Logic.ProperSublogic L Logic.Univ := ⟨by constructor <;> simp⟩

end LO.Modal

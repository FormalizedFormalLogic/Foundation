module

public import Foundation.Modal.Neighborhood2.Basic

@[expose] public section

namespace LO.Modal

namespace NeighborhoodModel

variable {ν : Type*} [Nonempty ν] {α : Type*}
         {M : NeighborhoodModel ν α}

class ContainsUnit (M : NeighborhoodModel ν α) : Prop where
  contains_unit : M.box Set.univ = Set.univ

export ContainsUnit (contains_unit)
attribute [simp, grind .] contains_unit

variable [M.ContainsUnit]

@[simp, grind .]
lemma mem_univ_filter {x} : Set.univ ∈ M.filter x := Set.eq_univ_iff_forall.mp contains_unit x

@[simp, grind .]
lemma validate_axiomN : M ⊧ Axioms.N := by grind;

end NeighborhoodModel

end LO.Modal

end

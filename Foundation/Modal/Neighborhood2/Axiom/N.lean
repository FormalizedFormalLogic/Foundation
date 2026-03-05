module

public import Foundation.Modal.Neighborhood2.Basic

@[expose] public section

namespace LO.Modal

variable {ν : Type*} [Nonempty ν] {α : Type*}

namespace NeighborhoodSystem

class ContainsUnit (M : NeighborhoodSystem ν α) : Prop where
  contains_unit : M.box Set.univ = Set.univ

export ContainsUnit (contains_unit)
attribute [simp, grind .] contains_unit

variable {N : NeighborhoodSystem ν α}

section

variable [ContainsUnit N]

@[simp, grind .]
lemma mem_univ_filter {x} : Set.univ ∈ N x := Set.eq_univ_iff_forall.mp contains_unit x

@[simp, grind .]
lemma validates_axiomN : N ⊧ Axioms.N := by grind;

end

lemma containsUnit_of_validates_axiomN (h : N ⊧ Axioms.N) : N.ContainsUnit := by
  constructor;
  apply Set.eq_univ_of_forall;
  intro x;
  simpa using @h (λ _ => Set.univ) x;

end NeighborhoodSystem

end LO.Modal

end

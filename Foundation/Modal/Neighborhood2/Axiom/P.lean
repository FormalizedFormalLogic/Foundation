module

public import Foundation.Modal.Neighborhood2.Basic

@[expose] public section

namespace LO.Modal

variable {ν : Type*} [Nonempty ν] {α : Type*}

namespace NeighborhoodSystem

class NotContainsEmpty (N : NeighborhoodSystem ν α) : Prop where
  not_contains_empty : N.box ∅ = ∅

export NotContainsEmpty (not_contains_empty)
attribute [simp, grind .] not_contains_empty

variable {N : NeighborhoodSystem ν α}

section

variable [NotContainsEmpty N]

@[simp, grind .]
lemma not_mem_box_empty : x ∉ N.box ∅ := by simp [N.not_contains_empty];

@[simp, grind .]
lemma mem_dia_univ : x ∈ N.dia Set.univ := by simp [NeighborhoodSystem.dia]

@[simp, grind .]
lemma validates_axiomP : N ⊧ Axioms.P := by grind;

end

lemma notContainsEmpty_of_validates_axiomP (h : N ⊧ Axioms.P) : N.NotContainsEmpty := by
  constructor;
  apply Set.eq_empty_of_forall_notMem;
  intro x;
  simpa using @h (λ _ => ∅) x;

end NeighborhoodSystem

end LO.Modal

end

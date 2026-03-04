module

public import Foundation.Modal.Neighborhood2.Basic

@[expose] public section

namespace LO.Modal

namespace NeighborhoodModel

variable {ν : Type*} [Nonempty ν] {α : Type*}
         {M : NeighborhoodModel ν α}

class NotContainsEmpty (M : NeighborhoodModel ν α) : Prop where
  not_contains_empty : M.box ∅ = ∅

export NotContainsEmpty (not_contains_empty)
attribute [simp, grind .] not_contains_empty

variable [M.NotContainsEmpty]

@[simp, grind .]
lemma not_mem_box_empty : x ∉ M.box ∅ := by simp [M.not_contains_empty];

@[simp, grind .]
lemma mem_dia_univ : x ∈ M.dia Set.univ := by simp [dia]

@[simp, grind .]
lemma validates_axiomP : M ⊧ Axioms.P := by grind;

lemma notContainsEmpty_of_m (h : F ⊧ Axioms.P) : F.NotContainsEmpty := by
  constructor;
  intro x;
  have := @h (λ _ => ∅) x;
  simpa [Satisfies] using this;

end NeighborhoodModel

end LO.Modal

end

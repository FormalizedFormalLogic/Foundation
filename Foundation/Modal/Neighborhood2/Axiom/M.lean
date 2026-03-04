module

public import Foundation.Modal.Neighborhood2.Basic

@[expose] public section

namespace LO.Modal

namespace NeighborhoodModel

variable {ν : Type*} [Nonempty ν] {α : Type*}
         {M : NeighborhoodModel ν α}

class IsMonotonic (M : NeighborhoodModel ν α) : Prop where
  monotonic : ∀ X Y : M.Neighborhood, M.box (X ∩ Y) ⊆ M.box X ∩ M.box Y

export IsMonotonic (monotonic)

variable [M.IsMonotonic]

@[simp, grind <=]
lemma box_subset_of_subset {X Y : M.Neighborhood} (h : X ⊆ Y) : M.box X ⊆ M.box Y := by
  intro x hx;
  have := M.monotonic X Y;
  rw [(show X ∩ Y = X by tauto_set)] at this;
  tauto_set;

lemma validates_axiomM : M ⊧ Axioms.M φ ψ := by grind [monotonic]

end NeighborhoodModel

end LO.Modal

end

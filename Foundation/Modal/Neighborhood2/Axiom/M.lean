module

public import Foundation.Modal.Neighborhood2.Basic

@[expose] public section

namespace LO.Modal

namespace NeighborhoodSystem

variable {ν : Type*} [Nonempty ν] {α : Type*}
         {N : NeighborhoodSystem ν α}

class IsMonotonic (M : NeighborhoodSystem ν α) : Prop where
  monotonic : ∀ X Y : M.Neighborhood, M.box (X ∩ Y) ⊆ M.box X ∩ M.box Y

export IsMonotonic (monotonic)

section

variable [N.IsMonotonic]

@[simp, grind <=]
lemma box_subset_of_subset {X Y : N.Neighborhood} (h : X ⊆ Y) : N.box X ⊆ N.box Y := by
  intro x hx;
  have := N.monotonic X Y;
  rw [(show X ∩ Y = X by tauto_set)] at this;
  tauto_set;

lemma validates_axiomM : N ⊧ Axioms.M φ ψ := by grind [monotonic]

end

lemma isMonotonic_of_validates_axiomM
  [DecidableEq α] (a b : α) (hab : a ≠ b)
  (h : N ⊧ Axioms.M (.atom a) (.atom b)) : N.IsMonotonic := by
  constructor;
  rintro X Y x hx;
  have := @h (λ p => if p = a then X else if p = b then Y else ∅) x;
  grind;

end NeighborhoodSystem

end LO.Modal

end

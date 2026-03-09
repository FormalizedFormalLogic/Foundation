module

public import Foundation.Modal.Neighborhood2.Basic

@[expose] public section

namespace LO.Modal

namespace NeighborhoodSystem

variable {ν : Type*} [Nonempty ν] {α : Type*}
         {N : NeighborhoodSystem ν α}

class HasPropertyK (N : NeighborhoodSystem ν α) : Prop where
  prop_K : ∀ X Y : N.Neighborhood, N.box (Xᶜ ∪ Y) ∩ N.box X ⊆ N.box Y

export HasPropertyK (prop_K)

section

@[simp, grind .]
lemma validates_axiomK [N.HasPropertyK] : N ⊧ Axioms.K φ ψ := by grind [prop_K]

end

lemma isMonotonic_of_validates_axiomK
  [DecidableEq α] (a b : α) (hab : a ≠ b)
  (h : N ⊧ Axioms.K (.atom a) (.atom b)) : N.HasPropertyK := by
  constructor;
  rintro X Y x hx;
  grind [h (λ p => if p = a then X else Y) x];

end NeighborhoodSystem

end LO.Modal

end

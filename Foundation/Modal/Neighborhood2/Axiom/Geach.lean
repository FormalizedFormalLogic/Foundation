module

public import Foundation.Modal.Neighborhood2.Basic

@[expose] public section

namespace LO.Modal

namespace NeighborhoodSystem

variable {ν : Type*} [Nonempty ν] {α : Type*}
         {N : NeighborhoodSystem ν α}

class HasPropertyGeach (i j m n : ℕ) (N : NeighborhoodSystem ν α) : Prop where
  prop_Geach : ∀ X : N.Neighborhood, N.dia^[i] (N.box^[m] X) ⊆ N.box^[j] (N.dia^[n] X)

export HasPropertyGeach (prop_Geach)

section

@[simp, grind .]
lemma validates_axiomG [N.HasPropertyGeach i j m n] : N ⊧ Axioms.Geach ⟨i, j, m, n⟩ φ := by
  intro V x;
  grind [prop_Geach (N := N) (i := i) (j := j) (m := m) (n := n) (X := NeighborhoodModel.truthset (M := ⟨N, V⟩) φ)];

end

lemma hasPropertyGeach_of_validates_axiomGeach
  (h : N ⊧ Axioms.Geach ⟨i, j, m, n⟩ (.atom a)) : N.HasPropertyGeach i j m n := by
  constructor;
  intro X x;
  grind [@h (λ _ => X) x];

end NeighborhoodSystem

end LO.Modal

end

module

public import Foundation.Modal.Neighborhood2.Axiom.C

@[expose] public section

namespace LO.Modal

variable {ν} [Nonempty ν] {α : Type*}
         {n : ℕ} {φ ψ χ : Formula α} {a : α}

namespace NeighborhoodSystem

variable {N : NeighborhoodSystem ν α} {X Y : N.Neighborhood} {x : N.World}

open Classical

def intersectionClosure (N : NeighborhoodSystem ν α) : NeighborhoodSystem ν α
  := ⟨λ x X => ∃ Ys : Finset _, Ys ≠ ∅ ∧ X = ⋂ Y ∈ Ys, Y ∧ ∀ Y ∈ Ys, Y ∈ N x⟩

@[grind <=]
lemma mem_intersection_box_of_mem_box (h : x ∈ N.box X) : x ∈ N.intersectionClosure.box X := by
  use {X};
  simp_all [box];

instance : N.intersectionClosure.IsRegular := by
  constructor;
  rintro X Y x ⟨⟨FX, _, rfl, _⟩, ⟨FY, _, rfl, _⟩⟩;
  use FX ∪ FY;
  refine ⟨?_, ?_, ?_⟩;
  . grind;
  . ext y;
    simp [Set.mem_inter_iff, Set.mem_iInter, Finset.mem_union];
    grind;
  . grind;

end NeighborhoodSystem

end LO.Modal

end

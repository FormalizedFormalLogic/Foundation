module

public import Foundation.Modal.Neighborhood2.Axiom.M
public import Foundation.Modal.Neighborhood2.Axiom.N
public import Foundation.Modal.Neighborhood2.Axiom.C

@[expose] public section

namespace LO.Modal

variable {ν} [Nonempty ν] {α : Type*}
         {n : ℕ} {φ ψ χ : Formula α} {a : α}

namespace NeighborhoodSystem

variable {N : NeighborhoodSystem ν α} {X Y : N.Neighborhood} {x : N.World}

def supplementation (N : NeighborhoodSystem ν α) : NeighborhoodSystem ν α
  := ⟨λ w => { X | ∃ Y ∈ N w, Y ⊆ X }⟩

@[grind =]
lemma iff_mem_supplementation_box_exists_subset : x ∈ N.supplementation.box X ↔ ∃ Y ⊆ X, x ∈ N.box Y := by
  simp [supplementation, box];
  tauto;

@[grind <=]
lemma mem_supplementation_box_of_mem_box : x ∈ N.box X → x ∈ N.supplementation.box X := by
  simp [supplementation, box];
  tauto;

instance : N.supplementation.IsMonotonic := by
  apply instIsMonotonic_of_box_subset_of_subset;
  grind;

instance [N.ContainsUnit] : N.supplementation.ContainsUnit := by
  constructor;
  apply Set.eq_univ_of_forall;
  intro;
  use Set.univ;
  grind;

instance [N.IsRegular] : N.supplementation.IsRegular := by
  constructor;
  rintro X Y _ ⟨hX, hY⟩;
  obtain ⟨X', _, _⟩ := iff_mem_supplementation_box_exists_subset.mp hX;
  obtain ⟨Y', _, _⟩ := iff_mem_supplementation_box_exists_subset.mp hY;
  apply iff_mem_supplementation_box_exists_subset.mpr;
  use X' ∩ Y';
  constructor;
  . tauto_set;
  . apply N.regular;
    grind;

end NeighborhoodSystem

end LO.Modal

end

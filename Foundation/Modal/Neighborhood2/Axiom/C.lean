module

public import Foundation.Modal.Neighborhood2.Basic

@[expose] public section

namespace LO.Modal

namespace NeighborhoodModel

variable {ν : Type*} [Nonempty ν] {α : Type*}
         {M : NeighborhoodModel ν α}

class IsRegular (M : NeighborhoodModel ν α) : Prop where
  regular : ∀ X Y : M.Neighborhood, (M.box X) ∩ (M.box Y) ⊆ M.box (X ∩ Y)

export IsRegular (regular)

variable [M.IsRegular]

open Classical in
lemma regular_finset_iUnion (s : Finset M.Neighborhood) (hs : s.Nonempty)
  : (⋂ i ∈ s, M.box i) ⊆ M.box (⋂ i ∈ s, i) := by
  induction s using Finset.induction_on with
  | empty => simp_all only [Finset.not_nonempty_empty];
  | insert i s hi ih =>
    wlog hs : s.Nonempty;
    . simp_all;
    apply Set.Subset.trans;
    . show ⋂ j ∈ insert i s, M.box j ⊆ M.box i ∩ M.box (⋂ j ∈ s, j);
      simp;
      grind;
    . rw [(show ⋂ j ∈ insert i s, j = i ∩ ⋂ j ∈ s, j by simp)]
      apply M.regular;

open Classical in
lemma regular_finite_iUnion {ι} [Fintype ι] [Nonempty ι] {X : ι → M.Neighborhood}
  : (⋂ i : ι, M.box (X i)) ⊆ M.box (⋂ i : ι, X i) := by
  simpa using regular_finset_iUnion (Finset.univ.image X) (by simp);

@[simp, grind .]
lemma validates_axiomC : M ⊧ Axioms.C φ ψ := by grind [regular];

end NeighborhoodModel

end LO.Modal

end

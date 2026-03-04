module

public import Foundation.Modal.Neighborhood2.Basic

@[expose] public section

namespace LO.Modal

variable {ν : Type*} [Nonempty ν] {α : Type*}

namespace NeighborhoodSystem

variable {N : NeighborhoodSystem ν α}

class IsRegular (N : NeighborhoodSystem ν α) : Prop where
  regular : ∀ X Y : N.Neighborhood, (N.box X) ∩ (N.box Y) ⊆ N.box (X ∩ Y)

export IsRegular (regular)

section

variable [N.IsRegular]

open Classical in
lemma regular_finset_iUnion (s : Finset N.Neighborhood) (hs : s.Nonempty)
  : (⋂ i ∈ s, N.box i) ⊆ N.box (⋂ i ∈ s, i) := by
  induction s using Finset.induction_on with
  | empty => simp_all only [Finset.not_nonempty_empty];
  | insert i s hi ih =>
    wlog hs : s.Nonempty;
    . simp_all;
    apply Set.Subset.trans;
    . show ⋂ j ∈ insert i s, N.box j ⊆ N.box i ∩ N.box (⋂ j ∈ s, j);
      simp;
      grind;
    . rw [(show ⋂ j ∈ insert i s, j = i ∩ ⋂ j ∈ s, j by simp)]
      apply N.regular;

open Classical in
lemma regular_finite_iUnion {ι} [Fintype ι] [Nonempty ι] {X : ι → N.Neighborhood}
  : (⋂ i : ι, N.box (X i)) ⊆ N.box (⋂ i : ι, X i) := by
  simpa using regular_finset_iUnion (Finset.univ.image X) (by simp);

@[simp, grind .]
lemma validates_axiomC : N ⊧ Axioms.C φ ψ := by grind [regular];

end

lemma isRegular_of_validates_axiomC
  [DecidableEq α] (a b : α) (hab : a ≠ b)
  (h : N ⊧ Axioms.C (.atom a) (.atom b)) : N.IsRegular := by
  constructor;
  rintro X Y w ⟨hwX, hwY⟩;
  have := h (λ p => if p = a then X else if p = b then Y else ∅) w;
  grind;

end NeighborhoodSystem

end LO.Modal

end

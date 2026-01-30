module

public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Algebra.Order.Ring.Nat

@[expose]
public section

namespace Finset

variable {α} {s t : Finset α}

lemma ssubset_of_subset_lt_card
  (h_subset : s ⊆ t)
  (h_card_le : s.card < t.card) : s ⊂ t := by
  constructor;
  . assumption;
  . by_contra hC;
    have : t = s := Finset.eq_iff_card_le_of_subset hC |>.mp (by omega);
    subst this;
    simp at h_card_le;

lemma eq_card_of_eq (h : s = t) : s.card = t.card := by tauto;

lemma sum_le_card
  {n} {f : α → ℕ}
  (hf : ∀ a ∈ s, f a ≤ n)
  : (∑ a ∈ s, f a) ≤ s.card * n :=
  calc
    _ ≤ (∑ x ∈ s, n) := by apply Finset.sum_le_sum hf
    _ = s.card * n   := by simp_all;

end Finset

end

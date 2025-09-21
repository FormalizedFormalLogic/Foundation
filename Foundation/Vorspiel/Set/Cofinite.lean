import Mathlib.Data.Finset.Insert
import Mathlib.Data.Set.Insert
import Mathlib.Data.Set.Countable
import Mathlib.Tactic.TautoSet

namespace Set

variable {α : Type*} {s t : Set α} {a b : α}

abbrev Cofinite (s : Set α) := sᶜ.Finite

abbrev Coinfinite (s : Set α) := sᶜ.Infinite

@[grind]
lemma iff_cofinite_not_coinfinite : s.Cofinite ↔ ¬s.Coinfinite := by simp;

@[simp] lemma iff_cofinite_comp_finite : s.Cofinite ↔ sᶜ.Finite := by simp [Cofinite];

@[simp] lemma iff_coinfinite_comp_infinite : s.Coinfinite ↔ sᶜ.Infinite := by simp [Coinfinite];

@[grind]
lemma Cofinite.subset (h : s ⊆ t) : s.Cofinite → t.Cofinite := by
  intro h;
  apply Set.Finite.subset (s := sᶜ) h;
  tauto_set;

@[grind]
lemma Coinfinite.subset (h : t ⊆ s) : s.Coinfinite → t.Coinfinite := by
  contrapose!;
  suffices t.Cofinite → s.Cofinite by grind;
  grind;

@[simp, grind] lemma univ_cofinite : (Set.univ (α := α)).Cofinite := by simp [Set.Cofinite];

@[grind]
lemma cofinite_union_left (hs : s.Cofinite) : (s ∪ t).Cofinite := by
  simp only [Cofinite, compl_union];
  apply Set.Finite.inter_of_left;
  assumption;

@[grind]
lemma cofinite_union_right (ht : t.Cofinite) : (s ∪ t).Cofinite := by
  exact (show (t ∪ s) = (s ∪ t) by tauto_set) ▸ cofinite_union_left ht;

end Set

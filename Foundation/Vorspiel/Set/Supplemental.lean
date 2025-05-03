import Mathlib.Data.Finset.Insert
import Mathlib.Data.Set.Insert

namespace Set

variable {α : Type*} {s t : Set α} {a b : α}

lemma doubleton_subset : ({a, b} : Set α) ⊆ s ↔ a ∈ s ∧ b ∈ s := by
  constructor;
  . intro h;
    have ⟨ha, hb⟩ := Set.insert_subset_iff.mp h;
    tauto;
  . rintro ⟨ha, hb⟩;
    apply Set.insert_subset_iff.mpr;
    constructor;
    . assumption;
    . simpa;

lemma iff_subset_insert_subset_diff : s ⊆ insert a t ↔ s \ {a} ⊆ t := by
  constructor;
  . intro ha b hb;
    rcases ha hb.1 with (rfl | hb);
    . simp at hb;
    . assumption;
  . intro ha b hb;
    apply or_iff_not_imp_left.mpr
    intro h;
    apply ha;
    constructor;
    . assumption;
    . simpa;

end Set

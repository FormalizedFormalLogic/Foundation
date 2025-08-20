import Mathlib.Data.Finset.Insert

namespace Finset

variable {α : Type*} [DecidableEq α] {a b : α} {s : Finset α}

lemma doubleton_subset : ({a, b} : Finset α) ⊆ s ↔ a ∈ s ∧ b ∈ s := by
  constructor
  . intro h
    have ⟨ha, hb⟩ := Finset.insert_subset_iff.mp h
    tauto
  . rintro ⟨ha, hb⟩
    apply Finset.insert_subset_iff.mpr
    constructor
    . assumption
    . simpa

end Finset

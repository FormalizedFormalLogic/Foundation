module
import Mathlib.Data.Finset.Insert

namespace Finset

variable {α : Type*} {a b : α} {s : Finset α}

lemma doubleton_subset [DecidableEq α] : ({a, b} : Finset α) ⊆ s ↔ a ∈ s ∧ b ∈ s := by
  constructor;
  . intro h;
    have ⟨ha, hb⟩ := Finset.insert_subset_iff.mp h;
    tauto;
  . rintro ⟨ha, hb⟩;
    apply Finset.insert_subset_iff.mpr;
    constructor;
    . assumption;
    . simpa;

/-
  Thanks to @plp127

  https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/ascending.2Fdecending.20lemmata.20related.20.60Set.60.20and.20.60Finset.60/near/539367015
-/
lemma no_ssubset_descending_chain  {f : ℕ → Finset α} : ¬(∀ i, ∃ j > i, f j ⊂ f i) := by
  intro h
  have n := 0
  induction hf : f n using WellFoundedLT.fix generalizing n with subst hf | _ _ ih
  obtain ⟨m, -, hy⟩ := h n
  exact ih (f m) hy m rfl

end Finset

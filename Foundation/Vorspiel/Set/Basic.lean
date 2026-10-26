module

public import Mathlib.Data.Set.Countable
public import Mathlib.Tactic.TautoSet
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Order.Filter.Ultrafilter.Defs

@[expose]
public section

namespace Set

variable {α : Type*} {s t : Set α} {a b : α}

/-
  Thanks to @plp127

  https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/ascending.2Fdecending.20lemmata.20related.20.60Set.60.20and.20.60Finset.60/near/539292838
-/
lemma infinitely_finset_approximate (count : s.Countable) (inf : s.Infinite) (ha : a ∈ s) :
  ∃ f : ℕ → Finset α, ((f 0) = {a}) ∧ (∀ i, f i ⊂ f (i + 1)) ∧ (∀ i, ↑(f i) ⊆ s) ∧
    (∀ b ∈ s, ∃ i, b ∈ f i) := by
  let X' := s \ {a}
  have count' : Countable X' := (count.mono Set.sdiff_subset).to_subtype
  have inf' : Infinite X' := (inf.sdiff (Set.finite_singleton a)).to_subtype
  obtain ⟨eq⟩ : Nonempty (Nat ≃ X') := nonempty_equiv_of_countable
  refine ⟨
    fun n => Finset.cons a ((Finset.range n).map
    (eq.toEmbedding.trans (Function.Embedding.subtype _))) ?_, ?_, ?_, ?_, ?_
  ⟩
  · suffices ∀ x < n, ¬↑(eq x) = a by simpa;
    intro x _
    exact (eq x).prop.right
  · rfl
  · simp [Finset.ssubset_def]
  · suffices ∀ (i : ℕ), Set.Iio i ⊆ (fun a ↦ ↑(eq a)) ⁻¹' s by simpa [Set.insert_subset_iff, ha]
    intro i x _;
    exact (eq x).prop.left
  · intro b hb
    by_cases hba : b = a
    · exact ⟨0, by simp [hba]⟩
    · refine ⟨eq.symm ⟨b, hb, hba⟩ + 1, ?_⟩
      apply Finset.mem_cons_of_mem;
      suffices ∃ a_1 < eq.symm ⟨b, _⟩ + 1, ↑(eq _) = b by simpa;
      exact ⟨eq.symm ⟨b, hb, hba⟩, by simp⟩

lemma subset_mem_chain_of_finite (c : Set (Set α)) (hc : Set.Nonempty c)
    (hchain : IsChain (· ⊆ ·) c) {s} (hfin : Set.Finite s) : s ⊆ ⋃₀ c → ∃ t ∈ c, s ⊆ t :=
  Set.Finite.induction_on s hfin
    (by rcases hc with ⟨t, ht⟩; intro; exact ⟨t, ht, by simp⟩)
    (by intro a s _ _ ih h
        have : ∃ t ∈ c, s ⊆ t := ih (subset_trans (Set.subset_insert a s) h)
        rcases this with ⟨t, htc, ht⟩
        have : ∃ u ∈ c, a ∈ u := by
          have : (∃ t ∈ c, a ∈ t) ∧ s ⊆ ⋃₀ c := by simpa [Set.insert_subset_iff] using h
          exact this.1
        rcases this with ⟨u, huc, hu⟩
        have : ∃ z ∈ c, t ⊆ z ∧ u ⊆ z := IsChain.directedOn hchain t htc u huc
        rcases this with ⟨z, hzc, htz, huz⟩
        exact ⟨z, hzc, Set.insert_subset (huz hu) (Set.Subset.trans ht htz)⟩)

end Set

end

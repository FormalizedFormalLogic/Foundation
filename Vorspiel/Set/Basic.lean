module

public import Mathlib.Data.Finset.Insert
public import Mathlib.Data.Set.Insert
public import Mathlib.Data.Set.Countable
public import Mathlib.Tactic.TautoSet
public import Mathlib.Data.Set.Finite.Range
public import Mathlib.Order.Filter.Ultrafilter.Defs
public import Vorspiel.Rel.CWF

@[expose]
public section

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

lemma ssubset_of_subset_ne (h : s ⊆ t) (hne : s ≠ t) : s ⊂ t := by
  constructor;
  . assumption;
  . revert hne;
    contrapose!;
    intro _;
    apply Set.eq_of_subset_of_subset <;> assumption;

/-
  Thanks to @plp127

  https://leanprover.zulipchat.com/#narrow/channel/217875-Is-there-code-for-X.3F/topic/ascending.2Fdecending.20lemmata.20related.20.60Set.60.20and.20.60Finset.60/near/539292838
-/
lemma infinitely_finset_approximate (count : s.Countable) (inf : s.Infinite) (ha : a ∈ s) :
  ∃ f : ℕ → Finset α, ((f 0) = {a}) ∧ (∀ i, f i ⊂ f (i + 1)) ∧ (∀ i, ↑(f i) ⊆ s) ∧ (∀ b ∈ s, ∃ i, b ∈ f i) := by
  let X' := s \ {a}
  have count' : Countable X' := (count.mono Set.diff_subset).to_subtype
  have inf' : Infinite X' := (inf.diff (Set.finite_singleton a)).to_subtype
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

lemma subset_mem_chain_of_finite (c : Set (Set α)) (hc : Set.Nonempty c) (hchain : IsChain (· ⊆ ·) c)
    {s} (hfin : Set.Finite s) : s ⊆ ⋃₀ c → ∃ t ∈ c, s ⊆ t :=
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

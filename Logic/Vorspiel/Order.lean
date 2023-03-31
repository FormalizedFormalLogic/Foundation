import Logic.Vorspiel.Vorspiel

variable {α : Sort u} (r : α → α → Prop)

local infix:50 " ≺ " => r

def IsInfiniteDescendingChain (c : ℕ → α) : Prop := ∀ i, c (i + 1) ≺ c i

noncomputable def descendingChain (z : α) : ℕ → α
  | 0       => z
  | (i + 1) => @Classical.epsilon α ⟨z⟩ (fun y => y ≺ descendingChain z i ∧ ¬Acc r y)

lemma not_acc_iff {x : α} : ¬Acc r x ↔ ∃ y, y ≺ x ∧ ¬Acc r y :=
  ⟨by contrapose; simp; exact Acc.intro x, by contrapose; simp; rintro ⟨h⟩; assumption⟩

@[simp] lemma descending_chain_zero (z : α) : descendingChain r z 0 = z := rfl

lemma isInfiniteDescendingChain_of_non_acc (z : α) (hz : ¬Acc r z) :
    IsInfiniteDescendingChain r (descendingChain r z) := by
  have : ∀ i, (i ≠ 0 → descendingChain r z i ≺ descendingChain r z i.pred) ∧ ¬Acc r (descendingChain r z i) := by
    intro i; induction' i with i ih
    · simpa using hz
    · simp[descendingChain]
      have : ∃ y, y ≺ (descendingChain r z i) ∧ ¬Acc r y := (not_acc_iff r).mp ih.2
      exact Classical.epsilon_spec this
  intro i; simpa using (this (i + 1)).1

theorem has_infiniteDescendingChain_of_not_wellFounded (h : ¬WellFounded r) : ∃ c, IsInfiniteDescendingChain r c := by
  have : ∃ z, ¬Acc r z := by
    suffices : ¬∀ z, Acc r z; exact not_forall.mp this
    intros h; have : WellFounded r := ⟨h⟩; contradiction
  rcases this with ⟨z, hz⟩
  exact ⟨descendingChain r z, isInfiniteDescendingChain_of_non_acc r z hz⟩


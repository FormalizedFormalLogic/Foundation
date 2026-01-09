module
import Foundation.Vorspiel.Vorspiel

section

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
    · simp [descendingChain]
      have : ∃ y, y ≺ (descendingChain r z i) ∧ ¬Acc r y := (not_acc_iff r).mp ih.2
      exact Classical.epsilon_spec this
  intro i; simpa using (this (i + 1)).1

end

section HeytingAlgebra

variable {α : Type*} [HeytingAlgebra α]

@[simp, grind .]
lemma himp_himp_inf_himp_inf_le (a b c : α) : (a ⇨ b ⇨ c) ⊓ (a ⇨ b) ⊓ a ≤ c := calc
  (a ⇨ b ⇨ c) ⊓ (a ⇨ b) ⊓ a = (a ⇨ b ⇨ c) ⊓ b ⊓ a := by simp only [inf_assoc, himp_inf_self]
  _                         = (a ⇨ b ⇨ c) ⊓ a ⊓ b := by simp only [inf_assoc, inf_comm a b]
  _                         ≤ (b ⇨ c) ⊓ b         := by simp only [himp_inf_self a (b ⇨ c), le_inf_iff]
                                                        constructor
                                                        · simp only [inf_assoc, inf_le_left]
                                                        · exact inf_le_right
  _                         ≤ c                   := by simp

@[simp, grind .]
lemma himp_inf_himp_inf_sup_le (a b c : α) : (a ⇨ c) ⊓ (b ⇨ c) ⊓ (a ⊔ b) ≤ c := by
  have ha : a ≤ (a ⇨ c) ⊓ (b ⇨ c) ⇨ c := by
    simp only [le_himp_iff, ← inf_assoc, inf_himp]
    refine inf_le_of_left_le (by simp)
  have hb : b ≤ (a ⇨ c) ⊓ (b ⇨ c) ⇨ c := by
    simp only [le_himp_iff, inf_comm (a ⇨ c) (b ⇨ c), ← inf_assoc, inf_himp]
    refine inf_le_of_left_le (by simp)
  have : a ⊔ b ≤ (a ⇨ c) ⊓ (b ⇨ c) ⇨ c := sup_le_iff.mpr ⟨ha, hb⟩
  simpa only [GeneralizedHeytingAlgebra.le_himp_iff, inf_comm (a ⊔ b)] using this

end HeytingAlgebra

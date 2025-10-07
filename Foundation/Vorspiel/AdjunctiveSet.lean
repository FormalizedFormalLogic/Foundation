
import Foundation.Vorspiel.Vorspiel

class Adjoin (β : outParam Type*) (α : Type*) where
  adjoin : β → α → α
export Adjoin (adjoin)

instance (α : Type*) : Adjoin α (Set α) := ⟨insert⟩

instance (α : Type*) : Adjoin α (List α) := ⟨List.cons⟩

instance (α : Type*) : Adjoin α (Multiset α) := ⟨Multiset.cons⟩

instance (α : Type*) [DecidableEq α] : Adjoin α (Finset α) := ⟨insert⟩

class AdjunctiveSet (β : outParam Type*) (α : Type*) extends Membership β α, HasSubset α, EmptyCollection α, Adjoin β α where
  subset_iff {a b : α} : a ⊆ b ↔ ∀ x ∈ a, x ∈ b
  not_mem_empty (x : β) : ¬x ∈ (∅ : α)
  mem_cons_iff {x z : β} {a : α} : x ∈ adjoin z a ↔ x = z ∨ x ∈ a

attribute [simp] AdjunctiveSet.not_mem_empty AdjunctiveSet.mem_cons_iff

instance Set.adjunctiveSet : AdjunctiveSet α (Set α) where
  subset_iff := iff_of_eq Set.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin]

instance List.adjunctiveSet : AdjunctiveSet α (List α) where
  subset_iff := List.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin]

instance Multiset.adjunctiveSet : AdjunctiveSet α (Multiset α) where
  subset_iff := Multiset.subset_iff
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin]

instance Finset.adjunctiveSet [DecidableEq α] : AdjunctiveSet α (Finset α) where
  subset_iff := Finset.subset_iff
  not_mem_empty := by simp
  mem_cons_iff := by simp [Adjoin.adjoin]

namespace AdjunctiveSet

variable {β α : Type*} [AdjunctiveSet β α]

def set : α → Set β := fun a ↦ {x | x ∈ a}

@[simp] lemma mem_set_iff {x : β} {a : α} : x ∈ (set a : Set β) ↔ x ∈ a := by simp [set]

lemma subset_iff_set_subset_set {a b : α} : a ⊆ b ↔ set a ⊆ set b := by simp [subset_iff, set]

@[simp, refl] lemma subset_refl (a : α) : a ⊆ a := subset_iff_set_subset_set.mpr (Set.Subset.refl _)

@[trans] lemma subset_trans {a b c : α} (ha : a ⊆ b) (hb : b ⊆ c) : a ⊆ c :=
  subset_iff_set_subset_set.mpr (Set.Subset.trans (subset_iff_set_subset_set.mp ha) (subset_iff_set_subset_set.mp hb))

lemma subset_antisymm {a b : α} (ha : a ⊆ b) (hb : b ⊆ a) : set a = set b :=
  Set.Subset.antisymm (subset_iff_set_subset_set.mp ha) (subset_iff_set_subset_set.mp hb)

@[simp] lemma empty_subset (a : α) : ∅ ⊆ a := by simp [subset_iff]

@[simp] lemma mem_cons (a : α) (x : β) : x ∈ adjoin x a := by simp [mem_cons_iff]

@[simp] lemma subset_cons (a : α) (x : β) : a ⊆ adjoin x a := by simp [subset_iff, mem_cons_iff]; tauto

@[simp] lemma set_empty : set (∅ : α) = ∅ := by ext; simp [set]

@[simp] lemma set_cons (z : β) (a : α) : set (adjoin z a) = insert z (set a) := by ext; simp [set]

def Finite (a : α) : Prop := (set a).Finite

@[simp] lemma empty_finite : Finite (∅ : α) := by simp [Finite]

lemma Finite.of_subset {a b : α} (ha : Finite a) (h : b ⊆ a) : Finite b :=
  Set.Finite.subset ha (subset_iff_set_subset_set.mp h)

@[simp] lemma cons_finite_iff {z : β} {a : α} : Finite (adjoin z a) ↔ Finite a :=
  ⟨fun h ↦ h.of_subset (by simp), by simpa [Finite] using Set.Finite.insert z⟩

def addList (a : α) : List β → α
  | [] => a
  | x :: xs => adjoin x (addList a xs)

def _root_.List.toAdjunctiveSet : List β → α
  | [] => ∅
  | x :: xs => adjoin x xs.toAdjunctiveSet

noncomputable def _root_.Finset.toAdjunctiveSet : Finset β → α := fun s ↦ s.toList.toAdjunctiveSet

@[simp] lemma mem_list_toAdjunctiveSet {x : β} {l : List β} : x ∈ (l.toAdjunctiveSet : α) ↔ x ∈ l := by
  induction l <;> simp [List.toAdjunctiveSet, *]

@[simp] lemma mem_finset_toAdjunctiveSet {x : β} {s : Finset β} : x ∈ (s.toAdjunctiveSet : α) ↔ x ∈ s := by simp [Finset.toAdjunctiveSet]

@[simp] lemma list_toAdjunctiveSet_finite (l : List β) : Finite (l.toAdjunctiveSet : α) := by simp [Finite, set]

@[simp] lemma finset_toAdjunctiveSet_finite (s : Finset β) : Finite (s.toAdjunctiveSet : α) := by simp [Finite, set]

end AdjunctiveSet

namespace Set

variable {α : Type*}

lemma cons_eq (a : α) (s : Set α) : adjoin a s = insert a s := rfl

@[simp] lemma adjunctiveSet_set (s : Set α) : AdjunctiveSet.set s = s := rfl

@[simp] lemma adjunctiveSet_finite_iff (s : Set α) : AdjunctiveSet.Finite s ↔ s.Finite := by simp [AdjunctiveSet.Finite]

end Set

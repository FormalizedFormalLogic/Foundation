
import Logic.Vorspiel.Vorspiel

class Cons (β : outParam Type*) (α : Type*) where
  cons : β → α → α
export Cons (cons)

instance (α : Type*) : Cons α (Set α) := ⟨insert⟩

instance (α : Type*) : Cons α (List α) := ⟨List.cons⟩

instance (α : Type*) : Cons α (Multiset α) := ⟨Multiset.cons⟩

instance (α : Type*) [DecidableEq α] : Cons α (Finset α) := ⟨insert⟩

class Collection (β : outParam Type*) (α : Type*) extends Membership β α, HasSubset α, EmptyCollection α, Cons β α where
  subset_iff {a b : α} : a ⊆ b ↔ ∀ x ∈ a, x ∈ b
  not_mem_empty (x : β) : ¬x ∈ (∅ : α)
  mem_cons_iff {x z : β} {a : α} : x ∈ cons z a ↔ x = z ∨ x ∈ a

attribute [simp] Collection.not_mem_empty Collection.mem_cons_iff

instance Set.collection : Collection α (Set α) where
  subset_iff := iff_of_eq Set.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Cons.cons]

instance List.collection : Collection α (List α) where
  subset_iff := List.subset_def
  not_mem_empty := by simp
  mem_cons_iff := by simp [Cons.cons]

instance Multiset.collection : Collection α (Multiset α) where
  subset_iff := Multiset.subset_iff
  not_mem_empty := by simp
  mem_cons_iff := by simp [Cons.cons]

instance Finset.collection [DecidableEq α] : Collection α (Finset α) where
  subset_iff := Finset.subset_iff
  not_mem_empty := by simp
  mem_cons_iff := by simp [Cons.cons]

namespace Collection

variable {β α : Type*} [Collection β α]

def set : α → Set β := fun a ↦ {x | x ∈ a}

@[simp] lemma mem_set_iff {x : β} {a : α} : x ∈ (set a : Set β) ↔ x ∈ a := by simp [set]

lemma subset_iff_set_subset_set {a b : α} : a ⊆ b ↔ set a ⊆ set b := by simp [subset_iff, set]

@[simp, refl] lemma subset_refl (a : α) : a ⊆ a := subset_iff_set_subset_set.mpr (Set.Subset.refl _)

@[trans] lemma subset_trans {a b c : α} (ha : a ⊆ b) (hb : b ⊆ c) : a ⊆ c :=
  subset_iff_set_subset_set.mpr (Set.Subset.trans (subset_iff_set_subset_set.mp ha) (subset_iff_set_subset_set.mp hb))

lemma subset_antisymm {a b : α} (ha : a ⊆ b) (hb : b ⊆ a) : set a = set b :=
  Set.Subset.antisymm (subset_iff_set_subset_set.mp ha) (subset_iff_set_subset_set.mp hb)

@[simp] lemma empty_subset (a : α) : ∅ ⊆ a := by simp [subset_iff]

@[simp] lemma mem_cons (a : α) (x : β) : x ∈ cons x a := by simp [mem_cons_iff]

@[simp] lemma subset_cons (a : α) (x : β) : a ⊆ cons x a := by simp [subset_iff, mem_cons_iff]; tauto

@[simp] lemma set_empty : set (∅ : α) = ∅ := by ext; simp [set]

@[simp] lemma set_cons (z : β) (a : α) : set (cons z a) = insert z (set a) := by ext; simp [set]

def Finite (a : α) : Prop := (set a).Finite

@[simp] lemma empty_finite : Finite (∅ : α) := by simp [Finite]

lemma Finite.of_subset {a b : α} (ha : Finite a) (h : b ⊆ a) : Finite b :=
  Set.Finite.subset ha (subset_iff_set_subset_set.mp h)

@[simp] lemma cons_finite_iff {z : β} {a : α} : Finite (cons z a) ↔ Finite a :=
  ⟨fun h ↦ h.of_subset (by simp), by simpa [Finite] using Set.Finite.insert z⟩

def addList (a : α) : List β → α
  | [] => a
  | x :: xs => cons x (addList a xs)

def _root_.List.toCollection : List β → α
  | [] => ∅
  | x :: xs => cons x xs.toCollection

noncomputable def _root_.Finset.toCollection : Finset β → α := fun s ↦ s.toList.toCollection

@[simp] lemma mem_list_toCollection {x : β} {l : List β} : x ∈ (l.toCollection : α) ↔ x ∈ l := by
  induction l <;> simp [List.toCollection, *]

@[simp] lemma mem_finset_toCollection {x : β} {s : Finset β} : x ∈ (s.toCollection : α) ↔ x ∈ s := by simp [Finset.toCollection]

@[simp] lemma list_toCollection_finite (l : List β) : Finite (l.toCollection : α) := by simp [Finite, set]

@[simp] lemma finset_toCollection_finite (s : Finset β) : Finite (s.toCollection : α) := by simp [Finite, set]

end Collection

namespace Set

variable {α : Type*}

lemma cons_eq (a : α) (s : Set α) : cons a s = insert a s := rfl

@[simp] lemma collection_set (s : Set α) : Collection.set s = s := rfl

@[simp] lemma collection_finite_iff (s : Set α) : Collection.Finite s ↔ s.Finite := by simp [Collection.Finite]

end Set

module

public import Foundation.Vorspiel

/-!
# Coherence space for denotational semantics of logics

reference:
- Jean-Yves Girard, Proofs and Types
- nLab, coherence space, https://ncatlab.org/nlab/show/coherence+space
-/

@[expose] public section

namespace LO

/-- A coherence space is a set equipped with a coherence relation `⁐`, which is reflexive and symmetric. -/
class CoherenceSpace (α : Type*) where
  /-- A coherence relation -/
  Coherence : α → α → Prop
  reflexive : Reflexive Coherence
  symmetric : Symmetric Coherence

namespace CoherenceSpace

infix:40 " ⁐ " => Coherence

variable {α : Type*} [CoherenceSpace α]

instance : Std.Refl (α := α) Coherence := ⟨reflexive⟩

instance : Std.Symm (α := α) Coherence := ⟨symmetric⟩

@[simp, refl] protected lemma Coherence.refl (x : α) : x ⁐ x := reflexive x

lemma Coherence.symm {x y : α} : x ⁐ y → y ⁐ x := fun h ↦ symmetric h

@[grind =] lemma Coherence.symm_iff {x y : α} : x ⁐ y ↔ y ⁐ x := ⟨symm, symm⟩

def Incoherence (x y : α) : Prop := ¬x ⁐ y ∨ x = y

infix:40 (priority := high) " ≍ " => Incoherence

@[simp, refl] lemma Incoherence.refl (x : α) : x ≍ x := by simp [Incoherence]

lemma Incoherence.symm {x y : α} : x ≍ y → y ≍ x := by
  intro h; cases h
  · left; grind
  · right; simp_all

@[grind =] lemma Incoherence.symm_iff {x y : α} : x ≍ y ↔ y ≍ x := ⟨symm, symm⟩

instance : Std.Refl (α := α) Incoherence := ⟨Incoherence.refl⟩

instance : Std.Symm (α := α) Incoherence := ⟨fun _ _ ↦ Incoherence.symm⟩

abbrev StrictIncoherence (x y : α) : Prop := ¬x ⁐ y

infix:40 " ⌣ " => StrictIncoherence

abbrev StrictCoherence (x y : α) : Prop := ¬x ≍ y

infix:40 " ⌢ " => StrictCoherence

end CoherenceSpace

/-! ### Cliques and cocliques -/

def IsClique [CoherenceSpace α] (s : Set α) : Prop := ∀ x ∈ s, ∀ y ∈ s, x ⁐ y

def IsCoclique [CoherenceSpace α] (s : Set α) : Prop := ∀ x ∈ s, ∀ y ∈ s, x ≍ y

def Clique (α : Type*) [CoherenceSpace α] : Set (Set α) := {s | IsClique s}

namespace IsClique

variable {α : Type*} [CoherenceSpace α]

@[simp] lemma emptyset : IsClique (∅ : Set α) := fun _ ↦ by simp

@[simp] lemma singleton (x : α) : IsClique {x} := by
  rintro _ rfl _ rfl; simp

lemma of_subset {s u : Set α} (hs : IsClique s) (h : u ⊆ s) : IsClique u :=
  fun x hx y hy ↦ hs x (h hx) y (h hy)

@[simp] lemma insert_iff {x : α} {s : Set α} : IsClique (insert x s) ↔ (∀ y ∈ s, x ⁐ y) ∧ IsClique s := by
  constructor
  · intro h
    refine ⟨fun y hy ↦ h x (by simp) y (by simp [hy]), h.of_subset <| by simp⟩
  · rintro ⟨h, hs⟩
    intro y hy z hz
    have hy : y = x ∨ y ∈ s := by simpa using hy
    have hz : z = x ∨ z ∈ s := by simpa using hz
    rcases hy with (rfl | hy_) <;> rcases hz with (rfl | hz_)
    · simp
    · exact h z hz_
    · exact symm (h y hy_)
    · exact hs y hy_ z hz_

@[simp] lemma doubleton_iff {x y : α} : IsClique {x, y} ↔ x ⁐ y := by simp

lemma sUnion_of_union {M : Set (Set α)} (h : ∀ a ∈ M, ∀ b ∈ M, IsClique (a ∪ b)) : IsClique (⋃₀ M) := by
  intro x ⟨a, ha, hx⟩ y ⟨b, hb, hy⟩
  exact h a ha b hb x (by simp [hx]) y (by simp [hy])

end IsClique

namespace Clique

open IsClique

variable {α : Type*} [CoherenceSpace α]

@[simp] lemma mem_clique_iff {s : Set α} : s ∈ Clique α ↔ IsClique s := by rfl

def colimit' (s : Set (Set α)) (h : ∀ a ∈ s, IsClique a) (directed : DirectedOn (· ⊆ ·) s) : Clique α :=
  ⟨⋃₀ s, sUnion_of_union fun a ha b hb ↦ by
    have : ∃ c ∈ s, a ⊆ c ∧ b ⊆ c := directed a ha b hb
    rcases this with ⟨c, hcs, hac, hbc⟩
    refine (h c hcs).of_subset (Set.union_subset hac hbc)⟩

def colimit (s : Set (Clique α)) (directed : DirectedOn (· ≤ ·) s) : Clique α :=
  colimit' s (by simp; tauto) (directedOn_onFun_iff.mp directed)

@[simp] lemma val_colimit (s : Set (Clique α)) (directed : DirectedOn (· ≤ ·) s) :
    (colimit s directed : Set α) = ⋃₀ s := by rfl

instance : Min (Clique α) := ⟨fun a b ↦ ⟨a ∩ b, a.prop.of_subset <| by simp⟩⟩

@[simp] lemma inf_def (a b : Clique α) : ((a ⊓ b : Clique α) : Set α) = ↑a ∩ ↑b := by rfl

@[simp] lemma prop_iff (a : Clique α) : IsClique (a : Set α) := a.prop

lemma le_def (a b : Clique α) : a ≤ b ↔ (a : Set α) ⊆ b := by rfl

end Clique

/-! ### Basic coherence spaces -/

instance : Bot (CoherenceSpace α) := ⟨{
  Coherence := Eq
  reflexive := refl
  symmetric _ _ := symm }⟩

instance : Top (CoherenceSpace α) := ⟨{
  Coherence _ _ := True
  reflexive _ := by trivial
  symmetric _ _ _ := by trivial }⟩

inductive CoherenceSpace.Top

inductive CoherenceSpace.Zero

instance : CoherenceSpace CoherenceSpace.Top := ⊥

instance : CoherenceSpace CoherenceSpace.Zero := ⊥

inductive CoherenceSpace.One where
  | star : CoherenceSpace.One

inductive CoherenceSpace.Bot where
  | absurd : CoherenceSpace.Bot

instance : CoherenceSpace CoherenceSpace.One := ⊤

instance : CoherenceSpace CoherenceSpace.Bot := ⊤

/-- A empty set is a coherence space -/
instance : CoherenceSpace PEmpty := ⊥

/-- A singleton set is a coherence space -/
instance : CoherenceSpace Unit := ⊥

/-- A doubleton set is a coherence space -/
instance : CoherenceSpace Bool := ⊥

/-! #### Additive conjunction -/

/-- An additive conjunction of two types -/
inductive With (α β : Type*) : Type _
  | inl : α → With α β
  | inr : β → With α β

infixr:30 (priority := low) " & " => With

namespace With

variable {α β : Type*} [CoherenceSpace α] [CoherenceSpace β]

inductive Coherence : α & β → α & β → Prop
  | inl {a₀ a₁ : α} : a₀ ⁐ a₁ → Coherence (inl a₀) (inl a₁)
  | inr {b₀ b₁ : β} : b₀ ⁐ b₁ → Coherence (inr b₀) (inr b₁)
  | inl_inr (a : α) (b : β) : Coherence (inl a) (inr b)
  | inr_inl (a : α) (b : β) : Coherence (inr b) (inl a)

/-- An additive conjunction of coherence spaces is also a coherence space -/
instance : CoherenceSpace (α & β) where
  Coherence p q := Coherence p q
  reflexive p := by
    rcases p
    · exact Coherence.inl (by rfl)
    · exact Coherence.inr (by rfl)
  symmetric p q := by
    rintro (h | h | _ | _)
    · exact Coherence.inl (symm h)
    · exact Coherence.inr (symm h)
    · exact Coherence.inr_inl _ _
    · exact Coherence.inl_inr _ _

lemma coherence_def (p q : α & β) : p ⁐ q ↔ Coherence p q := by rfl

end With

/-! #### Additive disjunction -/

/-- An additive disjunction of two types -/
inductive Plus (α β : Type*) : Type _
  | inl : α → Plus α β
  | inr : β → Plus α β

infixr:30 " ⨁ " => Plus

namespace Plus

variable {α β : Type*} [CoherenceSpace α] [CoherenceSpace β]

inductive Coherence : α ⨁ β → α ⨁ β → Prop
  | inl {a₀ a₁ : α} : a₀ ⁐ a₁ → Coherence (inl a₀) (inl a₁)
  | inr {b₀ b₁ : β} : b₀ ⁐ b₁ → Coherence (inr b₀) (inr b₁)

/-- An additive conjunction of coherence spaces is also a coherence space -/
instance : CoherenceSpace (α ⨁ β) where
  Coherence p q := Coherence p q
  reflexive p := by
    rcases p
    · exact Coherence.inl (by rfl)
    · exact Coherence.inr (by rfl)
  symmetric p q := by
    rintro (h | h)
    · exact Coherence.inl (symm h)
    · exact Coherence.inr (symm h)

lemma coherence_def (p q : α ⨁ β) : p ⁐ q ↔ Coherence p q := by rfl

end Plus

end LO

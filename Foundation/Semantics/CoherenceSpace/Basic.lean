import Foundation.Vorspiel.Vorspiel

/-!
# Coherence space for denotational semantics of logics

reference:
- Jean-Yves Girard, Proofs and Types
- nLab, coherence space, https://ncatlab.org/nlab/show/coherence+space
-/

namespace LO

/-- A coherence space is a set equipped with a coherence relation `◡`, which is reflexive and symmetric. -/
class CoherenceSpace (α : Type*) where
  /-- A coherence relation -/
  Rel : α → α → Prop
  reflexive : Reflexive Rel
  symmetric : Symmetric Rel

namespace CoherenceSpace

infix:40 " ◡ " => Rel

variable {α : Type*} [CoherenceSpace α]

instance : IsRefl α Rel := ⟨reflexive⟩

instance : IsSymm α Rel := ⟨symmetric⟩

@[simp, refl] protected lemma Rel.refl (x : α) : x ◡ x := reflexive x

@[grind .] lemma Rel.symm {x y : α} : x ◡ y → y ◡ x := fun h ↦ symmetric h

lemma Rel.symm_iff {x y : α} : x ◡ y ↔ y ◡ x := ⟨symm, symm⟩

end CoherenceSpace

/-! ### Cliques and cocliques -/

def IsClique [CoherenceSpace α] (s : Set α) : Prop := ∀ x ∈ s, ∀ y ∈ s, x ◡ y

def IsCoclique [CoherenceSpace α] (s : Set α) : Prop := ∀ x ∈ s, ∀ y ∈ s, x ◡ y → x = y

namespace IsClique

variable {α : Type*} [CoherenceSpace α]

@[simp] lemma emptyset : IsClique (∅ : Set α) := fun _ ↦ by simp

@[simp] lemma singleton (x : α) : IsClique {x} := by
  rintro _ rfl _ rfl; simp

lemma of_subset {s u : Set α} (hs : IsClique s) (h : u ⊆ s) : IsClique u :=
  fun x hx y hy ↦ hs x (h hx) y (h hy)

@[simp] lemma insert_iff {x : α} {s : Set α} : IsClique (insert x s) ↔ (∀ y ∈ s, x ◡ y) ∧ IsClique s := by
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

@[simp] lemma doubleton_iff {x y : α} : IsClique {x, y} ↔ x ◡ y := by simp

end IsClique

def Clique (α : Type*) [CoherenceSpace α] : Set (Set α) := {s | IsClique s}

--structure StableFunction (α β : Type*) [CoherenceSpace α] [CoherenceSpace β] where
--  toFun : Clique α → Clique β
--  monotone {a b : Clique α} : a ≤ b → toFun a ≤ toFun b
--  colimit (L : Set (Clique α)) (directed : DirectedOn (· ≤ ·) L) :
--      toFun L

instance : Bot (CoherenceSpace α) := ⟨{
  Rel := Eq
  reflexive := refl
  symmetric _ _ := symm }⟩

instance : Top (CoherenceSpace α) := ⟨{
  Rel _ _ := True
  reflexive _ := by trivial
  symmetric _ _ _ := by trivial }⟩

/-- A empty set is a coherence space -/
instance : CoherenceSpace PEmpty := ⊥

/-- A singleton set is a coherence space -/
instance : CoherenceSpace Unit := ⊥

/-- A doubleton set is a coherence space -/
instance : CoherenceSpace Bool := ⊥

/-- An additive conjunction, or a direct product of two types -/
inductive With (α β : Type*) : Type _
  | inl : α → With α β
  | inr : β → With α β

infixr:30 (priority := low) " & " => With

/-- An additive conjunction of coherence spaces is also a coherence space -/
instance [CoherenceSpace α] [CoherenceSpace β] : CoherenceSpace (α & β) where
  Rel p q :=
    match p, q with
    | .inl a₁, .inl a₂ => a₁ ◡ a₂
    | .inl a₁, .inr b₂ => True
    | .inr b₁, .inl a₂ => True
    | .inr b₁, .inr b₂ => b₁ ◡ b₂
  reflexive p := by rcases p <;> simp
  symmetric p q := by
    rcases p <;> rcases q <;> grind

end LO

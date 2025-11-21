import Foundation.Vorspiel.Vorspiel

namespace LO

class CoherenceSpace (α : Type*) where
  Rel : α → α → Prop
  reflexive : Reflexive Rel
  symmetric : Symmetric Rel

namespace CoherenceSpace

infix:40 " ◡ " => Rel

variable {α : Type*} [CoherenceSpace α]

instance : IsRefl α Rel := ⟨reflexive⟩

instance : IsSymm α Rel := ⟨symmetric⟩

@[simp, refl] protected lemma refl (x : α) : x ◡ x := reflexive x

@[symm] protected lemma symm {x y : α} : x ◡ y → y ◡ x := fun h ↦ symmetric h

@[symm] protected lemma symm_iff {x y : α} : x ◡ y ↔ y ◡ x := ⟨symm, symm⟩

def IsClique (A : Set α) : Prop := ∀ x ∈ A, ∀ y ∈ A, x ◡ y

def IsCoclique (A : Set α) : Prop := ∀ x ∈ A, ∀ y ∈ A, x ◡ y → x = y

end LO.CoherenceSpace

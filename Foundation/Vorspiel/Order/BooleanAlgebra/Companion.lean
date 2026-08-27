module

public import Foundation.Vorspiel.Order.BooleanAlgebra.Atoms
public import Mathlib.Order.BooleanSubalgebra

/-!
# Companion elements for extending a partial isomorphism

Given a finite Boolean subalgebra `A ≤ α`, an order isomorphism `e : A ≃o B` onto a
subalgebra `B ≤ β`, and an element `a : α`, a *companion* of `a` under `e` is an
element `b : β` that plays the same role with respect to `B` as `a` does with respect
to `A`: for every `w : A`, `w` is disjoint from (resp. below) `a` iff `e w` is disjoint
from (resp. below) `b`. When `β` is atomless every element admits a companion; this is
the key extension step of the back-and-forth construction in
`Foundation.Vorspiel.Order.BooleanAlgebra.Iso`.

Folklore Boolean algebra fact underlying the back-and-forth method; there is no direct
literature source.
-/

@[expose] public section

variable {α β : Type*} [BooleanAlgebra α] [BooleanAlgebra β]
  {A : BooleanSubalgebra α} {B : BooleanSubalgebra β}

/-- `b` is a companion of `a` under `e : A ≃o B`: every `w : A` relates to `a` (by
disjointness or by `≤`) exactly as `e w` relates to `b`. -/
def IsCompanion (e : A ≃o B) (a : α) (b : β) : Prop :=
  ∀ w : A, ((w : α) ⊓ a = ⊥ ↔ (e w : β) ⊓ b = ⊥) ∧ ((w : α) ≤ a ↔ (e w : β) ≤ b)

variable {e : A ≃o B} {a : α} {b : β}

/-- The companion relation is symmetric under swapping `e` for `e.symm`. -/
lemma IsCompanion.symm (h : IsCompanion e a b) : IsCompanion e.symm b a := by
  sorry

/-- If `A` is finite and `β` is a nontrivial densely ordered (equivalently, atomless)
Boolean algebra, every `a : α` admits a companion under `e`. -/
theorem exists_isCompanion [Nontrivial β] [DenselyOrdered β]
    (hA : (A : Set α).Finite) (e : A ≃o B) (a : α) :
    ∃ b : β, IsCompanion e a b := by
  sorry

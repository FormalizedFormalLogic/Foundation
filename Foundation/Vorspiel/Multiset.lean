module

public import Mathlib.Data.Multiset.AddSub
public import Mathlib.Tactic.Abel
public import Mathlib.Algebra.Order.Group.Multiset

@[expose] public section

namespace Multiset

/-- Function to avoid reducing `{a} + s` to `a ::ₘ s` -/
def atom (a : α) : Multiset α := {a}

/-- `⦃x, y, z, ...⦄` notation for `kpair` -/
syntax "⦃" term,* "⦄" : term

macro_rules
  | `(⦃$terms:term,*, $term:term⦄) => `(⦃$terms,*⦄ + atom $term)
  | `(⦃$term:term⦄) => `(atom $term)
  | `(⦃⦄) => `(0)

@[app_unexpander atom]
meta def pairUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term) => `(⦃$term⦄)
  | _ => throw ()

lemma atom_eq_singleton (a : α) : ⦃a⦄ = {a} := rfl

lemma add_atom_eq_cons (a : α) (s : Multiset α) : s + ⦃a⦄ = a ::ₘ s := by
  rw [atom_eq_singleton, add_comm]; simp

@[simp] lemma mem_atom_iff {a b : α} : a ∈ ⦃b⦄ ↔ a = b := by simp [atom_eq_singleton]

@[simp] lemma atom_subset_iff {a : α} {s : Multiset α} : ⦃a⦄ ≤ s ↔ a ∈ s := by simp [atom_eq_singleton]

@[simp] lemma map_atom (f : α → β) (a : α) : ⦃a⦄.map f = ⦃f a⦄ := by
  simp [atom_eq_singleton]

end Multiset

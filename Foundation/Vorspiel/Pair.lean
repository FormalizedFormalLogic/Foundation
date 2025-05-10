import Foundation.Vorspiel.Vorspiel

class Pair (α : Type*) where
  pair : α → α → α
  right : α → α
  left : α → α
  left_pair (x y : α) : left (pair x y) = x
  right_pair (x y : α) : right (pair x y) = y
  pair_left_right (x y : α) : pair (left x) (right x) = x

attribute [simp] Pair.left_pair Pair.right_pair Pair.pair_left_right

/-- `!⟪x, y, z, ...⟫` notation for `Seq` -/
syntax "⟪" term,* "⟫" : term

macro_rules
  | `(⟪$term:term, $terms:term,*⟫) => `(Pair.pair $term ⟪$terms,*⟫)
  | `(⟪$term:term⟫) => `($term)

@[app_unexpander Pair.pair]
def pairUnexpander : Lean.PrettyPrinter.Unexpander
  | `($_ $term $term2) => `(⟪$term, $term2⟫)
  | _ => throw ()

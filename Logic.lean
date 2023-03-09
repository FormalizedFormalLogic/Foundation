import Logic.Predicate.FirstOrder.Calculus
import Logic.Predicate.FirstOrder.Meta

open Language FirstOrder Derivation

def d : Derivation.Valid (L := oring) “(∀ ∀ (¬#0 < #1 → #1 ≤ #0)) → (&0 < &1 ∨ &1 ≤ &0)” := by prove 64
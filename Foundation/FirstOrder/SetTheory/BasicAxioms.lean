import Foundation.FirstOrder.SetTheory.Basic

namespace LO.FirstOrder.SetTheory

def isSubsetOf : Semisentence ℒₛₑₜ 2 := “x y. ∀ z ∈ x, z ∈ y”

syntax:45 first_order_term:45 " ⊆ " first_order_term:0 : first_order_formula

macro_rules
  | `(⤫formula[ $binders* | $fbinders* | $t:first_order_term ⊆ $u:first_order_term ]) =>
    `(isSubsetOf/[⤫term[ $binders* | $fbinders* | $t ], ⤫term[ $binders* | $fbinders* | $u ]])

def Axiom.empty : Sentence ℒₛₑₜ := “∃ x, ∀ y, y ∉ x”

def Axiom.extentionality : Sentence ℒₛₑₜ := “∀ x y, x = y ↔ ∀ z, z ∈ x ↔ z ∈ y”

def Axiom.pairing : Sentence ℒₛₑₜ := “∀ x y, ∃ z, x ∈ z ∧ y ∈ z ∧ ∀ w ∈ z, w = x ∨ w = y”

def Axiom.union : Sentence ℒₛₑₜ := “∀ x, ∃ y, ∀ z, z ∈ y ↔ ∃ w ∈ x, z ∈ w”

def Axiom.power : Sentence ℒₛₑₜ := “∀ x, ∃ y, ∀ z, z ∈ y ↔ z ⊆ x”

end LO.FirstOrder.SetTheory

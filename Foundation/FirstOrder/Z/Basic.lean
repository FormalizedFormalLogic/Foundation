import Foundation.FirstOrder.SetTheory.Basic

/-!
# Zermelo set theory

reference: Ralf Schindler, "Set Theory, Exploring Independence and Truth"
-/

namespace LO.FirstOrder.SetTheory

def isSubsetOf : Semisentence ℒₛₑₜ 2 := “x y. ∀ z ∈ x, z ∈ y”

syntax:45 first_order_term:45 " ⊆ " first_order_term:0 : first_order_formula

macro_rules
  | `(⤫formula[ $binders* | $fbinders* | $t:first_order_term ⊆ $u:first_order_term ]) =>
    `(isSubsetOf/[⤫term[ $binders* | $fbinders* | $t ], ⤫term[ $binders* | $fbinders* | $u ]])

def isEmpty : Semisentence ℒₛₑₜ 1 := “x. ∀ y, y ∉ x”

def isSucc : Semisentence ℒₛₑₜ 2 := “y x. ∀ z, z ∈ y ↔ z ∈ x ∨ z = x”

namespace Axiom

def empty : Sentence ℒₛₑₜ := “∃ e, ∀ y, y ∉ e”

def extentionality : Sentence ℒₛₑₜ := “∀ x y, x = y ↔ ∀ z, z ∈ x ↔ z ∈ y”

def pairing : Sentence ℒₛₑₜ := “∀ x y, ∃ z, ∀ w, w ∈ z ↔ w = x ∨ w = y”

def union : Sentence ℒₛₑₜ := “∀ x, ∃ y, ∀ z, z ∈ y ↔ ∃ w ∈ x, z ∈ w”

def power : Sentence ℒₛₑₜ := “∀ x, ∃ y, ∀ z, z ∈ y ↔ z ⊆ x”

def infinity : Sentence ℒₛₑₜ := “∃ I, (∀ e, !isEmpty e → e ∈ I) ∧ (∀ x x', !isSucc x' x ∧ x ∈ I → x' ∈ I)”

def foundation : Sentence ℒₛₑₜ := “∀ x, ¬!isEmpty x → ∃ y ∈ x, ∀ z ∈ x, z ∉ y”

def separationSchema (φ : SyntacticSemiformula ℒₛₑₜ 1) : Sentence ℒₛₑₜ :=
  ∀∀₀ “∀ x, ∃ y, ∀ z, z ∈ y ↔ z ∈ x ∧ !φ z”

def replacementSchema (φ : SyntacticSemiformula ℒₛₑₜ 2) : Sentence ℒₛₑₜ :=
  ∀∀₀ “(∀ x, ∃! y, !φ x y) → ∀ X, ∃ Y, ∀ y, y ∈ Y ↔ ∃ x ∈ X, !φ x y”

def choice : Sentence ℒₛₑₜ :=
  “∀ x, (∀ y ∈ x, ¬!isEmpty y) ∧ (∀ y ∈ x, ∀ z ∈ x, y ≠ z → ¬∃ w, w ∈ y ∧ w ∈ z) → ∃ c, ∀ y ∈ x, ∃ u ∈ c, u ∈ y”

end Axiom

end FirstOrder.SetTheory

open FirstOrder SetTheory

inductive Zermelo : Theory ℒₛₑₜ
  | equal : ∀ φ ∈ 𝗘𝗤, Zermelo φ
  | empty : Zermelo Axiom.empty
  | extentionality : Zermelo Axiom.extentionality
  | pairing : Zermelo Axiom.pairing
  | union : Zermelo Axiom.union
  | power : Zermelo Axiom.power
  | infinity : Zermelo Axiom.infinity
  | foundation : Zermelo Axiom.foundation
  | separation (φ : SyntacticSemiformula ℒₛₑₜ 1) : Zermelo (Axiom.separationSchema φ)

notation "𝗭" => Zermelo

namespace Zermelo

instance : 𝗘𝗤 ⪯ 𝗭 := Entailment.WeakerThan.ofSubset Zermelo.equal



end Zermelo

end LO

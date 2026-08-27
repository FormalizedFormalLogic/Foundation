module

public import Mathlib.Order.BooleanAlgebra.Basic

/-!
# Auxiliary identities for Boolean algebras

Elementary Boolean algebra identities used to build the back-and-forth
isomorphism between countable atomless Boolean algebras
(`Foundation.Vorspiel.Order.BooleanAlgebra.Iso`).

Folklore Boolean algebra manipulations; there is no direct literature source.
-/

@[expose] public section

namespace BooleanAlgebra

variable {γ : Type*} [BooleanAlgebra γ]

/-- Comparing `y₁ ⊓ a` and `y₂ ⊓ a` reduces to the vanishing of the relative
complement `(y₁ \ y₂) ⊓ a`. -/
lemma inf_le_iff_sdiff_disjoint {y₁ y₂ a : γ} : y₁ ⊓ a ≤ y₂ ⊓ a ↔ (y₁ \ y₂) ⊓ a = ⊥ := by
  sorry

/-- Comparing the normal-form representatives `(y ⊓ a) ⊔ (z ⊓ aᶜ)` of an element of
`closure (insert a A)` splits into independent comparisons on the `a`-part and the
`aᶜ`-part. -/
lemma insertRep_le_insertRep_iff {y₁ z₁ y₂ z₂ a : γ} :
    (y₁ ⊓ a) ⊔ (z₁ ⊓ aᶜ) ≤ (y₂ ⊓ a) ⊔ (z₂ ⊓ aᶜ) ↔
      (y₁ \ y₂) ⊓ a = ⊥ ∧ (z₁ \ z₂) ⊓ aᶜ = ⊥ := by
  sorry

/-- The complement of a normal-form representative `(y ⊓ a) ⊔ (z ⊓ aᶜ)` is again a
normal-form representative, with `y` and `z` complemented. -/
lemma compl_insertRep (y z a : γ) : ((y ⊓ a) ⊔ (z ⊓ aᶜ))ᶜ = (yᶜ ⊓ a) ⊔ (zᶜ ⊓ aᶜ) := by
  sorry

end BooleanAlgebra

module

public import Foundation.Vorspiel.Order.BooleanAlgebra.PartialIso

/-!
# Countable atomless Boolean algebras are isomorphic

Any two countable, nontrivial, atomless (equivalently, densely ordered) Boolean
algebras are order isomorphic. The proof is a back-and-forth argument on
`PartialIso α β`, modeled on `Order.iso_of_countable_dense`
(`Mathlib.Order.CountableDenseLinearOrder`): a generic ideal in the poset of partial
isomorphisms, obtained from `Order.idealOfCofinals`, is directed and meets every
`PartialIso.definedAtLeft`/`PartialIso.definedAtRight`, hence assembles into a total
order isomorphism `α ≃o β`.

Analogue, for Boolean algebras, of Cantor's isomorphism theorem for countable dense
linear orders; there is no direct literature source for the Boolean algebra case.
-/

@[expose] public section

open PartialIso

/-- Any two countable, nontrivial, atomless (densely ordered) Boolean algebras are
order isomorphic. -/
theorem iso_of_countable_atomless
    {α β : Type*}
    [BooleanAlgebra α] [Countable α] [Nontrivial α] [DenselyOrdered α]
    [BooleanAlgebra β] [Countable β] [Nontrivial β] [DenselyOrdered β] :
    Nonempty (α ≃o β) := by
  sorry

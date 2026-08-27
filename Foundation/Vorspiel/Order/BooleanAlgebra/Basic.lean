module

public import Mathlib.Order.Atoms
public import Mathlib.Order.Atoms.Finite
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Auxiliary identities and atom theory for Boolean algebras

Elementary Boolean algebra identities and finite-atom-theory facts used to build the
back-and-forth isomorphism between countable atomless Boolean algebras
(`Foundation.Vorspiel.Order.BooleanAlgebra.Iso`): comparing normal-form
representatives `(y ⊓ a) ⊔ (z ⊓ aᶜ)` reduces to comparing relative complements, and
every element of a finite Boolean algebra is the supremum of the atoms lying below it.

Folklore Boolean algebra manipulations; there is no direct literature source.
-/

@[expose] public section

namespace BooleanAlgebra

variable {γ : Type*} [BooleanAlgebra γ]

/-- Comparing `y₁ ⊓ a` and `y₂ ⊓ a` reduces to the vanishing of the relative
complement `(y₁ \ y₂) ⊓ a`. -/
lemma inf_le_iff_sdiff_disjoint {y₁ y₂ a : γ} : y₁ ⊓ a ≤ y₂ ⊓ a ↔ (y₁ \ y₂) ⊓ a = ⊥ := by
  rw [← sdiff_eq_bot_iff,
    show (y₁ ⊓ a) \ (y₂ ⊓ a) = y₁ \ y₂ ⊓ a by
      rw [sdiff_eq, sdiff_eq, compl_inf, inf_sup_left]; simp [inf_left_comm, inf_comm]]

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

/-- An atom `p` is either below `w`, or disjoint from it. -/
lemma IsAtom.le_or_disjoint {p : γ} (hp : IsAtom p) (w : γ) : p ≤ w ∨ p ⊓ w = ⊥ := by
  sorry

open Classical in
/-- The (finite) set of atoms lying below `w`. -/
noncomputable def atomsBelow [Fintype γ] (w : γ) : Finset γ :=
  {p | IsAtom p ∧ p ≤ w}

/-- Every element of a finite Boolean algebra is the supremum of the atoms below it. -/
lemma sup_atomsBelow_eq [Finite γ] (w : γ) :
    haveI := Fintype.ofFinite γ
    (atomsBelow w).sup id = w := by
  sorry

/-- An element `a'` is disjoint from `w` iff it is disjoint from every atom below `w`. -/
lemma inf_eq_bot_iff_atomsBelow [Finite γ] {w a' : γ} :
    haveI := Fintype.ofFinite γ
    w ⊓ a' = ⊥ ↔ ∀ p ∈ atomsBelow w, p ⊓ a' = ⊥ := by
  sorry

end BooleanAlgebra

namespace BooleanSubalgebra

variable {α : Type*} [BooleanAlgebra α] {A : BooleanSubalgebra α}

/-- Coercion into the ambient algebra commutes with finite suprema. -/
lemma val_finsetSup (s : Finset A) : ((s.sup id : A) : α) = s.sup (fun p => (p : α)) := by
  sorry

end BooleanSubalgebra

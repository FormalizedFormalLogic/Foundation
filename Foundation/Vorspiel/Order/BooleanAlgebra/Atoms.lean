module

public import Mathlib.Order.Atoms
public import Mathlib.Order.Atoms.Finite
public import Mathlib.Order.BooleanSubalgebra
public import Mathlib.Data.Finset.Lattice.Fold

/-!
# Atoms of a finite Boolean algebra

Every element of a finite Boolean algebra is the supremum of the atoms lying below it.
This is used, together with `DenselyOrdered`, to construct a "companion" element for the
back-and-forth extension lemma in
`Foundation.Vorspiel.Order.BooleanAlgebra.Companion`.

Folklore Boolean algebra fact (finite Boolean algebras are atomic and atomistic);
there is no direct literature source.
-/

@[expose] public section

namespace BooleanAlgebra

variable {γ : Type*} [BooleanAlgebra γ]

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

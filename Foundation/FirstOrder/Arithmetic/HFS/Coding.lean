module

public import Foundation.FirstOrder.Arithmetic.HFS.Vec

@[expose] public section
namespace LO.FirstOrder.Arithmetic

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def finsetArithmetizeAux : List V → V
  |      [] => ∅
  | x :: xs => insert x (finsetArithmetizeAux xs)

@[simp] lemma finsetArithmetizeAux_nil : finsetArithmetizeAux ([] : List V) = ∅ := rfl

@[simp] lemma finsetArithmetizeAux_cons (x : V) (xs) :
    finsetArithmetizeAux (x :: xs) = insert x (finsetArithmetizeAux xs) := rfl

@[simp] lemma mem_finsetArithmetizeAux_iff {x : V} {s : List V} :
    x ∈ finsetArithmetizeAux s ↔ x ∈ s := by induction s <;> simp [*]

noncomputable def _root_.Finset.arithmetize (s : Finset V) : V := finsetArithmetizeAux s.toList

@[simp] lemma mem_finsetArithmetize_iff {x : V} {s : Finset V} :
    x ∈ s.arithmetize ↔ x ∈ s := by
  simp [Finset.arithmetize]

@[simp] lemma finset_empty_arithmetize : (∅ : Finset V).arithmetize = ∅ := by
  simp [Finset.arithmetize]

@[simp] lemma finset_insert_arithmetize (a : V) (s : Finset V) :
    (insert a s).arithmetize = insert a s.arithmetize := mem_ext <| by
  intro x; simp

end LO.FirstOrder.Arithmetic

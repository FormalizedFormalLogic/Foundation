import Arithmetization.ISigmaOne.HFS.Vec

/-!

# Vec

-/

noncomputable section

namespace LO.Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈𝚺₁]

def finsetArithmetizeAux : List V → V
  | []      => ∅
  | x :: xs => insert x (finsetArithmetizeAux xs)

@[simp] lemma finsetArithmetizeAux_nil : finsetArithmetizeAux ([] : List V) = ∅ := rfl

@[simp] lemma finsetArithmetizeAux_cons (x : V) (xs) :
    finsetArithmetizeAux (x :: xs) = insert x (finsetArithmetizeAux xs) := rfl

@[simp] lemma mem_finsetArithmetizeAux_iff {x : V} {s : List V} :
    x ∈ finsetArithmetizeAux s ↔ x ∈ s := by induction s <;> simp [*]

def _root_.Finset.arithmetize (s : Finset V) : V := finsetArithmetizeAux s.toList

@[simp] lemma mem_finsetArithmetize_iff {x : V} {s : Finset V} :
    x ∈ s.arithmetize ↔ x ∈ s := by
  simp [Finset.arithmetize]

@[simp] lemma finset_empty_arithmetize : (∅ : Finset V).arithmetize = ∅ := by
  simp [Finset.arithmetize]

@[simp] lemma finset_insert_arithmetize (a : V) (s : Finset V) :
    (insert a s).arithmetize = insert a s.arithmetize := mem_ext <| by
  intro x; simp


end LO.Arith

end

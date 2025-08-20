
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.Fintype.Pigeonhole


@[simp] lemma Nat.sub_one_lt' [NeZero n] : n - 1 < n := sub_one_lt $ NeZero.ne n


namespace Fin

lemma isEmpty_embedding_lt (hn : n > m) : IsEmpty (Fin n ↪ Fin m) := by
  apply Function.Embedding.isEmpty_of_card_lt
  simpa

variable {n : ℕ} [NeZero n] {i : Fin n}

def last' : Fin n := ⟨n - 1, Nat.sub_one_lt'⟩

@[simp]
lemma lt_last' : i ≤ Fin.last' := by
  apply Nat.le_sub_one_of_lt
  apply Fin.is_lt

end Fin

module

public import Mathlib.Algebra.GroupWithZero.Nat
public import Mathlib.Data.Fintype.Pigeonhole

public section


@[simp, grind .]
lemma Nat.sub_one_lt' [NeZero n] : n - 1 < n := sub_one_lt $ NeZero.ne n


namespace Fin

variable {n : ℕ} {i : Fin n}

lemma isEmpty_embedding_lt (hn : n > m) : IsEmpty (Fin n ↪ Fin m) := by
  apply Function.Embedding.isEmpty_of_card_lt;
  simpa;

@[simp, grind .]
lemma lt_last : n < Fin.last (n + 1) := by
  induction n with
  | zero => simp;
  | succ n ih => simp;

@[grind <=]
lemma lt_sub_one_of_pos {a : Fin n} (hn : 0 < n) : a ≤ ⟨n - 1, by omega⟩ := by
  apply Nat.le_sub_one_of_lt;
  omega;


section last'

variable [NeZero n]

/-- The last element of `Fin n` when `n` is `NeZero`. -/
def last' [NeZero n] : Fin n := ⟨n - 1, Nat.sub_one_lt'⟩

@[simp, grind .]
lemma lt_last' : i ≤ Fin.last' := by
  apply Nat.le_sub_one_of_lt;
  apply Fin.is_lt;

end last'


end Fin

end

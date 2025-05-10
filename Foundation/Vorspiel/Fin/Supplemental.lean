
import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Data.Fintype.Pigeonhole


@[simp] lemma Nat.sub_one_lt' [NeZero n] : n - 1 < n := sub_one_lt $ NeZero.ne n


namespace Fin

lemma isEmpty_embedding_lt (hn : n > m) : IsEmpty (Fin n ↪ Fin m) := by
  apply Function.Embedding.isEmpty_of_card_lt;
  simpa;

section

variable {n : ℕ} [NeZero n] {i : Fin n}

def last' : Fin n := ⟨n - 1, Nat.sub_one_lt'⟩

@[simp]
lemma lt_last' : i ≤ Fin.last' := by
  apply Nat.le_sub_one_of_lt;
  apply Fin.is_lt;

end

section

lemma pos_of_coe_ne_zero {i : Fin (n + 1)} (h : (i : ℕ) ≠ 0) : 0 < i := Nat.pos_of_ne_zero h

@[simp] lemma one_pos'' : (0 : Fin (n + 2)) < 1 := pos_of_coe_ne_zero (Nat.succ_ne_zero 0)

@[simp] lemma two_pos : (0 : Fin (n + 3)) < 2 := pos_of_coe_ne_zero (Nat.succ_ne_zero 1)

@[simp] lemma three_pos : (0 : Fin (n + 4)) < 3 := pos_of_coe_ne_zero (Nat.succ_ne_zero 2)

@[simp] lemma four_pos : (0 : Fin (n + 5)) < 4 := pos_of_coe_ne_zero (Nat.succ_ne_zero 3)

@[simp] lemma five_pos : (0 : Fin (n + 6)) < 5 := pos_of_coe_ne_zero (Nat.succ_ne_zero 4)

end

end Fin

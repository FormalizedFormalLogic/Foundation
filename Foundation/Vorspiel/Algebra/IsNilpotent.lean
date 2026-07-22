module

public import Mathlib.Algebra.GroupWithZero.Basic

@[expose] public section

namespace IsNilpotent

variable {R : Type*} [MonoidWithZero R]

lemma rotate_mul {x y : R} (h : IsNilpotent (x * y)) : IsNilpotent (y * x) := by
  obtain ⟨n, hn⟩ := h
  refine ⟨n + 1, ?_⟩
  have shift : ∀ m : ℕ, (y * x) ^ (m + 1) = y * (x * y) ^ m * x := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [_root_.pow_succ (y * x) (m + 1), ih, _root_.pow_succ (x * y) m]
      simp [mul_assoc]
  rw [shift n, hn]
  simp

lemma rotate_mul_iff {x y : R} : IsNilpotent (x * y) ↔ IsNilpotent (y * x) :=
  ⟨rotate_mul, rotate_mul⟩

end IsNilpotent

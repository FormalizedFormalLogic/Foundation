import Mathlib.Order.Fin.Basic

namespace Fin.Fin1

variable {n : Fin 1}

@[simp]
lemma eq_one : n = 0 := by cases n; omega;

@[simp] lemma not_lt_zero : ¬0 < n := by simp [eq_one];


end Fin.Fin1

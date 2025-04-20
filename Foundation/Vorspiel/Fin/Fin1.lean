import Mathlib.Order.Fin.Basic

namespace Fin.Fin1

variable {n : Fin 1}

@[simp] lemma not_lt_zero : ¬0 < n := by simp;

end Fin.Fin1

import Mathlib.Data.Fin.Basic

example {P : Fin 4 → Prop} : P (Fin.succ (0 : Fin (1 + 1 + 1))) ↔ P 1 := by { simp }
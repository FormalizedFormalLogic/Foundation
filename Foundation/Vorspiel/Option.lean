module

public import Mathlib.Logic.Denumerable
public import Mathlib.Logic.Equiv.List

@[expose] public section

namespace Option

lemma pure_eq_some (a : α) : pure a = some a := rfl

@[simp]
lemma toList_eq_iff {o : Option α} {a} : o.toList = [a] ↔ o = some a := by
  rcases o <;> simp

end Option

end

module

public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace Empty

lemma eq_elim {α : Sort u} (f : Empty → α) : f = elim := funext (by rintro ⟨⟩)

end Empty

end

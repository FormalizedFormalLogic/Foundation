module

public import Mathlib.Basic.IsEmpty.Basic

@[expose] public section

namespace IsEmpty
variable {o : Sort*} (h : IsEmpty o)

lemma eq_elim' {α : Sort*} (f : o → α) : f = h.elim' := funext h.elim

lemma eq_elim {α : Sort*} (f : o → α) : f = h.elim := funext h.elim

end IsEmpty

end

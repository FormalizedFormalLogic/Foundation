module

public import Mathlib.Logic.IsEmpty

@[expose] public section

namespace IsEmpty
variable {o : Sort u} (h : IsEmpty o)

lemma eq_elim' {α : Sort*} (f : o → α) : f = h.elim' := funext h.elim

lemma eq_elim {α : Sort*} (f : o → α) : f = h.elim := funext h.elim

end IsEmpty

end

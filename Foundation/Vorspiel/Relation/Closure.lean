import Mathlib.Logic.Relation

namespace Relation

variable {α} {r : α → α → Prop}


namespace TransGen

instance : IsTrans α (TransGen r) := ⟨by apply TransGen.trans⟩

end TransGen



section Irrefl

def IrreflGen (r : α → α → Prop) := λ x y => x ≠ y ∧ r x y

instance : IsIrrefl α (IrreflGen r) := ⟨by simp [IrreflGen]⟩

end Irrefl


end Relation

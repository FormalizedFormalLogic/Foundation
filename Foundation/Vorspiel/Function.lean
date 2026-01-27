module

public import Mathlib.Data.Fintype.Basic

@[expose] public section

namespace Function

variable  {α : Type u} {β : Type v}

def funEqOn (φ : α → Prop) (f g : α → β) : Prop := ∀ a, φ a → f a = g a

lemma funEqOn.of_subset {φ ψ : α → Prop} {f g : α → β} (e : funEqOn φ f g) (h : ∀ a, ψ a → φ a) : funEqOn ψ f g :=
  by intro a ha; exact e a (h a ha)

end Function

end

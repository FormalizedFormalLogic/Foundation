import Mathlib.Data.Fintype.Defs

namespace Fintype

variable {ι : Type _} [Fintype ι]

def decideEqPi {β : ι → Type*} (a b : (i : ι) → β i) (_ : (i : ι) → Decidable (a i = b i)) : Decidable (a = b) :=
  decidable_of_iff (∀ i, a i = b i) funext_iff.symm

end Fintype

module

public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Fintype.Sigma
public import Mathlib.Data.Fintype.Vector

@[expose] public section

namespace Fintype
variable {ι : Type _} [Fintype ι]

section

variable {α : Type _} [SemilatticeSup α] [OrderBot α]

def sup (f : ι → α) : α := (Finset.univ : Finset ι).sup f

@[simp] lemma elem_le_sup (f : ι → α) (i : ι) : f i ≤ sup f := Finset.le_sup (by simp)

lemma le_sup {a : α} {f : ι → α} (i : ι) (le : a ≤ f i) : a ≤ sup f := le_trans le (elem_le_sup _ _)

@[simp] lemma sup_le_iff {f : ι → α} {a : α} :
    sup f ≤ a ↔ (∀ i, f i ≤ a) := by simp [sup]

@[simp] lemma finsup_eq_0_of_empty [IsEmpty ι] (f : ι → α) : sup f = ⊥ := by simp [sup]

end

def decideEqPi {β : ι → Type*} (a b : (i : ι) → β i) (_ : (i : ι) → Decidable (a i = b i)) : Decidable (a = b) :=
  decidable_of_iff (∀ i, a i = b i) funext_iff.symm

end Fintype

end

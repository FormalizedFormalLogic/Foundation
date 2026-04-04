module

public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.CompleteBooleanAlgebra

public section

variable {α : Type*} [Order.Frame α]

/-- https://github.com/leanprover-community/mathlib4/blob/205a0ba54c047cafda226494138ba715ab6bf28c/Mathlib/Order/CompleteBooleanAlgebra.lean#L413-L414-/
theorem iSup_himp_eq {f : ι → α} : (⨆ x, f x) ⇨ a = ⨅ x, f x ⇨ a :=
  eq_of_forall_le_iff fun b => by simp [inf_iSup_eq]

theorem compl_iSup' {a : ι → α} : (⨆ i, a i)ᶜ = ⨅ i, (a i)ᶜ := by
  simpa using iSup_himp_eq (f := a) (a := ⊥)

module

public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.CompleteBooleanAlgebra

public section

variable {α : Type*} [Order.Frame α]

theorem compl_iSup' {a : ι → α} : (⨆ i, a i)ᶜ = ⨅ i, (a i)ᶜ := by
  simpa using iSup_himp_eq (f := a) (a := ⊥)

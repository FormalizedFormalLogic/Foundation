module

public import Mathlib.Order.Heyting.Regular
public import Mathlib.Order.CompleteBooleanAlgebra

public section

namespace Heyting.Regular

variable {α : Type*} [Order.Frame α]

open Heyting Regular

instance completelattice : CompleteLattice (Regular α) where
  __ : Lattice (Regular α) := inferInstance
  __ := gi.liftCompleteLattice

instance : CompleteBooleanAlgebra (Regular α) where
  __ : BooleanAlgebra (Regular α) := inferInstance
  __ : CompleteLattice (Regular α) := inferInstance

theorem coe_sSup (s : Set (Regular α)) : (↑(sSup s) : α) = (sSup ((↑) '' s))ᶜᶜ := by
  simp [sSup, sSup_image]

theorem coe_iSup (a : ι → Regular α) : (↑(⨆ i, a i) : α) = (⨆ i, (a i : α))ᶜᶜ := calc
  (↑(⨆ i, a i) : α) = (↑(sSup (Set.range a)) : α) := by rfl
                  _ = (⨆ i, (a i : α))ᶜᶜ          := by rw [coe_sSup]; congr; grind

theorem coe_sInf (s : Set (Regular α)) : (↑(sInf s) : α) = sInf ((↑) '' s) := by
  simp [sInf, sInf_image]; rfl

theorem coe_iInf (a : ι → Regular α) : (↑(⨅ i, a i) : α) = (⨅ i, (a i : α)) := calc
  (↑(⨅ i, a i) : α) = (↑(sInf (Set.range a)) : α) := by rfl
                  _ = (⨅ i, (a i : α))          := by rw [coe_sInf]; congr; grind

end Heyting.Regular

module

public import Mathlib.Topology.Order.UpperLowerSetTopology
public import Mathlib.Topology.Sets.Opens
public import Mathlib.Order.Heyting.Regular
public import Foundation.Vorspiel.Order.Regular
public import Foundation.Vorspiel.Order.Dense

@[expose] public section

variable {α : Type*} [Preorder α]

namespace LowerSet

open Order

instance : HeytingAlgebra (LowerSet α) := inferInstance

lemma inf_eq_bot_iff_incompatible {u v : LowerSet α} : u ⊓ v = ⊥ ↔ (∀ x ∈ u, ∀ y ∈ v, x ⟂ y) := by
  suffices (u ∩ v : Set α) = ∅ ↔ ∀ x ∈ u, ∀ y ∈ v, x ⟂ y by simpa [LowerSet.ext_iff]
  constructor
  · rintro e x hx y hy ⟨z, hzx, hzy⟩
    have hzu : z ∈ u := u.lower hzx hx
    have hzv : z ∈ v := v.lower hzy hy
    have : z ∈ (u ∩ v : Set α) := ⟨hzu, hzv⟩
    simp_all
  · rintro h
    suffices ∀ x ∈ u, x ∉ v by
      apply Set.eq_empty_of_forall_notMem
      simpa
    intro x hx hx'
    simpa using h x hx x hx'

lemma mem_dual_iff {u : LowerSet α} : x ∈ uᶜ ↔ ∀ y ∈ u, x ⟂ y := by
  suffices (∃ i, (∀ y ∈ i, ∀ z ∈ u, y ⟂ z) ∧ x ∈ i) ↔ ∀ y ∈ u, x ⟂ y by simpa [Compl.compl, inf_eq_bot_iff_incompatible]
  constructor
  · rintro ⟨i, hi, hxi⟩ y hyu
    exact hi x hxi y hyu
  · intro h
    let i : LowerSet α := ⟨{x | ∀ y ∈ u, x ⟂ y}, by
      intro a b hba ha y hyu
      exact (ha y hyu).lower hba (by rfl)⟩
    refine ⟨i, by simp [i], by simpa [i] using h⟩

lemma coe_dual (u : LowerSet α) : uᶜ = {x | ∀ y ∈ u, x ⟂ y} := by
  ext x; simp [mem_dual_iff]

lemma mem_himp_iff {u v : LowerSet α} : x ∈ u ⇨ v ↔ ∀ y ≤ x, y ∈ u → y ∈ v := by
  suffices (∃ s, s ⊓ u ≤ v ∧ x ∈ s) ↔ ∀ y ≤ x, y ∈ u → y ∈ v by simpa [HImp.himp]
  constructor
  · rintro ⟨s, hs, hxs⟩ y hyx hyu
    have : y ∈ s := s.lower hyx hxs
    have : y ∈ s ⊓ u := ⟨this, hyu⟩
    exact hs this
  · intro h
    refine ⟨LowerSet.Iic x, ?_, by simp⟩
    intro y; simp; grind

variable (α)

abbrev Regular := Heyting.Regular (LowerSet α)

variable {α}

namespace Regular

instance : BooleanAlgebra (Regular α) := inferInstance

instance : CompleteBooleanAlgebra (Regular α) := inferInstance

end Regular

end LowerSet

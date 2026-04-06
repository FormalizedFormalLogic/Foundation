
module

public import Mathlib.Order.Ideal
public import Mathlib.Order.PFilter
public import Mathlib.Data.Finset.Lattice.Basic

@[expose] public section

namespace Order

namespace Ideal

variable  {P : Type*} [SemilatticeSup P] [OrderBot P]

lemma sSup_def (s : Set (Ideal P)) : sSup s = sInf (upperBounds s) := rfl

lemma iSup_def (I : ι → Ideal P) : ⨆ i, I i = sInf (upperBounds (Set.range I)) := rfl

@[simp] lemma mem_bot {x : P} : x ∈ (⊥ : Ideal P) ↔ x = ⊥ := le_bot_iff

theorem mem_finsup_principal [DecidableEq ι] {s : Finset ι} {f : ι → P} :
    x ∈ s.sup (principal ∘ f) ↔ x ≤ s.sup f := by
  induction s using Finset.induction generalizing x
  · simp
  case insert i s hi ih =>
    suffices (∃ y ≤ f i, ∃ z ≤ s.sup f, x ≤ y ⊔ z) ↔ x ≤ f i ⊔ s.sup f by
      simpa [ih]
    constructor
    · rintro ⟨y, hy, z, hz, h⟩
      refine le_trans h (sup_le_sup hy hz)
    · intro h
      exact ⟨f i, le_refl _, s.sup f, le_refl _, h⟩

lemma mem_iSup_iff [DecidableEq ι] {I : ι → Ideal P} {x : P} :
    x ∈ ⨆ i, I i ↔ ∃ u : Finset ι, x ∈ u.sup I := by
  revert x
  let K : Ideal P := {
    carrier := { x | ∃ u : Finset ι, x ∈ u.sup I }
    lower' x y hyx := by
      rintro ⟨u, hx⟩
      exact ⟨u, (u.sup I).lower hyx hx⟩
    nonempty' := ⟨⊥, ∅, by simp⟩
    directed' := by
      rintro x ⟨u, hu⟩ y ⟨v, hv⟩
      refine ⟨x ⊔ y, ⟨u ∪ v, ?_⟩, ?_⟩
      · simpa [Finset.sup_union]
        using ⟨⟨x, hu, y, hv, by simp⟩, ⟨x, hu, y, hv, by simp⟩⟩
      · simp }
  have mem_K_iff x : x ∈ K ↔ ∃ u : Finset ι, x ∈ u.sup I := by rfl
  suffices K = ⨆ i, I i by simp [←this, mem_K_iff]
  apply le_antisymm
  · intro x hx
    rcases hx with ⟨u, hxu⟩
    suffices ∀ J, (∀ i, I i ≤ J) → x ∈ J by simpa [iSup_def, upperBounds]
    intro J hJ
    have : u.sup I ≤ J := by simp [hJ]
    exact this hxu
  · suffices ∀ i, I i ≤ K by simpa [upperBounds]
    intro i x hx
    refine ⟨{i}, by simpa using hx⟩

end Ideal

end Order

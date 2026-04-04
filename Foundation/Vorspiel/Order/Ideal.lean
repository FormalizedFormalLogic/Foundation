
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

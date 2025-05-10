import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Union
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range

namespace Finset

variable {α : Type*} {a b : α} {s : Finset α}

lemma doubleton_subset [DecidableEq α] : ({a, b} : Finset α) ⊆ s ↔ a ∈ s ∧ b ∈ s := by
  constructor;
  . intro h;
    have ⟨ha, hb⟩ := Finset.insert_subset_iff.mp h;
    tauto;
  . rintro ⟨ha, hb⟩;
    apply Finset.insert_subset_iff.mpr;
    constructor;
    . assumption;
    . simpa;

noncomputable def rangeOfFinite {ι : Sort v} [Finite ι] (f : ι → α) : Finset α :=
  Set.Finite.toFinset (s := Set.range f) (Set.finite_range f)

lemma mem_rangeOfFinite_iff  {ι : Sort v} [Finite ι] {f : ι → α} {a : α} :
    a ∈ rangeOfFinite f ↔ ∃ i : ι, f i = a := by simp [rangeOfFinite]

noncomputable def imageOfFinset [DecidableEq β] (s : Finset α) (f : (a : α) → a ∈ s → β) : Finset β :=
  Finset.biUnion s (rangeOfFinite $ f ·)

lemma mem_imageOfFinset_iff [DecidableEq β] {s : Finset α} {f : (a : α) → a ∈ s → β} {b : β} :
    b ∈ imageOfFinset s f ↔ ∃ (a : α) (ha : a ∈ s), f a ha = b := by
  simp [imageOfFinset, mem_rangeOfFinite_iff]

@[simp] lemma mem_imageOfFinset  [DecidableEq β] {s : Finset α} (f : (a : α) → a ∈ s → β) (a : α) (ha : a ∈ s) :
    f a ha ∈ imageOfFinset s f := by simpa [mem_imageOfFinset_iff] using ⟨a, ha, rfl⟩

lemma erase_union [DecidableEq α] {a : α} {s t : Finset α} :
  (s ∪ t).erase a = (s.erase a) ∪ (t.erase a) := by ext; simp [and_or_left]

@[simp] lemma equiv_univ {α α'} [Fintype α] [Fintype α'] [DecidableEq α'] (e : α ≃ α') :
    (Finset.univ : Finset α).image e = Finset.univ := by ext x; simp

@[simp] lemma sup_univ_equiv {α α'} [DecidableEq α] [Fintype α] [Fintype α'] [SemilatticeSup β] [OrderBot β] (f : α → β) (e : α' ≃ α) :
    Finset.sup Finset.univ (fun i => f (e i)) = Finset.sup Finset.univ f := by
  simpa [Function.comp] using Eq.symm <| Finset.sup_image Finset.univ e f

lemma sup_univ_cast {α : Type _} [SemilatticeSup α] [OrderBot α] {n} (f : Fin n → α) (n') {h : n' = n} :
    Finset.sup Finset.univ (fun (i : Fin n') => f (i.cast h)) = Finset.sup Finset.univ f := by rcases h with rfl; simp

end Finset

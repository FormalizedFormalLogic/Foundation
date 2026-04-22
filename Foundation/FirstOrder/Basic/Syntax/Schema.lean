module

public import Foundation.FirstOrder.Basic.Syntax.Rew

@[expose] public section

/-!
# Schema

First-order schema `Schema L` is defined as a set of propositions, which may contains free variables.

-/

namespace LO.FirstOrder

abbrev Schema (L : Language) := Set (Proposition L)

abbrev Theory (L : Language) := Set (Sentence L)

namespace Schema

variable {L : Language}

@[coe] def ofProposition (φ : Proposition L) : Schema L := {φ}

instance : Coe (Proposition L) (Schema L) := ⟨fun φ ↦ ofProposition φ⟩

@[simp] lemma mem_coe (φ ψ : Proposition L) : ψ ∈ (φ : Schema L) ↔ ψ = φ := by rfl

instance : AdjunctiveSet (Proposition L) (Schema L) where
  Subset 𝔖₁ 𝔖₂ := 𝔖₁ ≤ 𝔖₂
  emptyCollection := ⊥
  adjoin φ 𝔖 := φ ⊔ 𝔖
  subset_iff := by simp [Set.subset_def]
  not_mem_empty _ := by simp
  mem_cons_iff := by simp

class IsClosed (𝔖 : Schema L) : Prop where
  closed : ∀ ω : Rew L ℕ 0 ℕ 0, ∀ φ ∈ 𝔖, ω ▹ φ ∈ 𝔖

namespace IsClosed

instance : IsClosed (⊤ : Schema L) where
  closed _ _ _ := by trivial

instance : IsClosed (⊥ : Schema L) where
  closed _ _ := by rintro ⟨⟩

instance sup (𝔖₁ 𝔖₂ : Schema L) [IsClosed 𝔖₁] [IsClosed 𝔖₂] : IsClosed (𝔖₁ ∪ 𝔖₂) where
  closed ω φ h := by
    have : φ ∈ 𝔖₁ ∨ φ ∈ 𝔖₂ := by simpa using h
    rcases this with (h |h )
    · left; apply IsClosed.closed ω φ h
    · right; apply IsClosed.closed ω φ h

instance inf (𝔖₁ 𝔖₂ : Schema L) [IsClosed 𝔖₁] [IsClosed 𝔖₂] : IsClosed (𝔖₁ ∩ 𝔖₂) where
  closed ω φ h := by
    have : φ ∈ 𝔖₁ ∧ φ ∈ 𝔖₂ := by simpa using h
    rcases this with ⟨h₁, h₂⟩
    constructor
    · apply IsClosed.closed ω φ h₁
    · apply IsClosed.closed ω φ h₂

lemma sSup (s : Set (Schema L)) (H : ∀ 𝔖 ∈ s, IsClosed 𝔖) : IsClosed (sSup s) where
  closed ω φ h := by
    have : ∃ 𝔖 ∈ s, φ ∈ 𝔖 := by simpa using h
    rcases this with ⟨𝔖, hs, hφ⟩
    have : IsClosed 𝔖 := H 𝔖 hs
    exact ⟨𝔖, hs, IsClosed.closed _ _ hφ⟩

instance sentence (σ : Sentence L) : IsClosed (σ : Schema L) where
  closed _ φ h := by
    have : φ = σ := by simpa using h
    rcases this
    simp

end IsClosed

@[coe] def uniClosure (𝔖 : Schema L) : Theory L := Set.image Semiformula.univCl {φ | φ ∈ 𝔖}

instance : Coe (Schema L) (Theory L) := ⟨uniClosure⟩

variable {𝔖 : Schema L}

@[simp] lemma mem_uniClosure :
    σ ∈ (𝔖 : Theory L) ↔ ∃ φ ∈ 𝔖, Semiformula.univCl φ = σ := by simp [uniClosure]

@[simp] lemma coe_sup (𝔖₁ 𝔖₂ : Schema L) : ((𝔖₁ ∪ 𝔖₂ : Schema L) : Theory L) = (𝔖₁ : Theory L) ∪ (𝔖₂ : Theory L) := by
  ext σ; simp [uniClosure]; grind

@[simp] lemma coe_sSup (s : Set (Schema L)) : ((sSup s : Schema L) : Theory L) = ⋃ 𝔖 ∈ s, (𝔖 : Theory L) := by
  ext σ; simp [uniClosure, sSup]; grind

@[simp] lemma coe_coe_proposition (φ : Proposition L) : ((φ : Schema L) : Theory L) = {φ.univCl} := by
  ext σ; simp [uniClosure]

@[grind <-] lemma coe_subset_coe_of_le {𝔖₁ 𝔖₂ : Schema L} (h : 𝔖₁ ≤ 𝔖₂) : (𝔖₁ : Theory L) ⊆ (𝔖₂ : Theory L) :=
  Set.image_mono h

end Schema

end LO.FirstOrder

end

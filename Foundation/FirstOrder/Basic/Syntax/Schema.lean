module

public import Foundation.FirstOrder.Basic.Syntax.Rew

@[expose] public section

/-!
# Schema

First-order schema `Schema L` is defined as a set of propositions, which may contains free variables.

-/

namespace LO.FirstOrder

structure Schema (L : Language) where
  Mem : Proposition L → Prop

abbrev Theory (L : Language) := Set (Sentence L)
namespace Schema

variable {L : Language}

instance : SetLike (Schema L) (Proposition L) where
  coe 𝓢 := { φ | 𝓢.Mem φ }
  coe_injective' := by
    rintro ⟨⟩ ⟨⟩ _
    congr

lemma mem_def (𝓢 : Schema L) (φ : Proposition L) : 𝓢.Mem φ ↔ φ ∈ 𝓢 := Iff.rfl

@[simp] lemma mem_mk_iff (φ : Proposition L) (P : Proposition L → Prop) : φ ∈ Schema.mk P ↔ P φ := Iff.rfl

lemma le_def (𝓢₁ 𝓢₂ : Schema L) : 𝓢₁ ≤ 𝓢₂ ↔ ∀ φ, φ ∈ 𝓢₁ → φ ∈ 𝓢₂ := Iff.rfl

instance : CompleteLattice (Schema L) where
  sup 𝓢₁ 𝓢₂ := ⟨fun φ ↦ φ ∈ 𝓢₁ ∨ φ ∈ 𝓢₂⟩
  le_sup_left _ _ := by simp [le_def]; grind
  le_sup_right _ _ := by simp [le_def]; grind
  sup_le _ _ _ := by simp [le_def]; grind
  inf 𝓢₁ 𝓢₂ := ⟨fun φ ↦ φ ∈ 𝓢₁ ∧ φ ∈ 𝓢₂⟩
  inf_le_left _ _ := by simp [le_def]; grind
  inf_le_right _ _ := by simp [le_def]
  le_inf _ _ _ := by simp [le_def]; grind
  sSup s := ⟨fun φ ↦ ∃ 𝓢 ∈ s, φ ∈ 𝓢⟩
  le_sSup _ _ := by simp [le_def]; grind
  sSup_le _ _ := by simp [le_def]; grind
  sInf s := ⟨fun φ ↦ ∀ 𝓢 ∈ s, φ ∈ 𝓢⟩
  sInf_le _ _ := by simp [le_def]; grind
  le_sInf _ _ := by simp [le_def]; grind
  top := ⟨fun _ ↦ True⟩
  le_top _ _ := by simp
  bot := ⟨fun _ ↦ False⟩
  bot_le _ _ := by simp

@[simp] lemma mem_sup_iff (𝓢₁ 𝓢₂ : Schema L) (φ : Proposition L) : φ ∈ 𝓢₁ ⊔ 𝓢₂ ↔ φ ∈ 𝓢₁ ∨ φ ∈ 𝓢₂ := Iff.rfl

@[simp] lemma mem_inf_iff (𝓢₁ 𝓢₂ : Schema L) (φ : Proposition L) : φ ∈ 𝓢₁ ⊓ 𝓢₂ ↔ φ ∈ 𝓢₁ ∧ φ ∈ 𝓢₂ := Iff.rfl

@[simp] lemma mem_sSup_iff (s : Set (Schema L)) (φ : Proposition L) : φ ∈ sSup s ↔ ∃ 𝓢 ∈ s, φ ∈ 𝓢 := Iff.rfl

@[simp] lemma mem_sInf_iff (s : Set (Schema L)) (φ : Proposition L) : φ ∈ sInf s ↔ ∀ 𝓢 ∈ s, φ ∈ 𝓢 := Iff.rfl

@[simp] lemma mem_top (φ : Proposition L) : φ ∈ (⊤ : Schema L) := by trivial

@[simp] lemma not_mem_bot (φ : Proposition L) : φ ∉ (⊥ : Schema L) := by rintro ⟨⟩

@[coe] def ofProposition (φ : Proposition L) : Schema L := ⟨(· = φ)⟩

instance : Coe (Proposition L) (Schema L) := ⟨fun φ ↦ ofProposition φ⟩

@[simp] lemma mem_coe (φ ψ : Proposition L) : ψ ∈ (φ : Schema L) ↔ ψ = φ := by rfl

instance : AdjunctiveSet (Proposition L) (Schema L) where
  Subset 𝓢₁ 𝓢₂ := 𝓢₁ ≤ 𝓢₂
  emptyCollection := ⊥
  adjoin φ 𝓢 := φ ⊔ 𝓢
  subset_iff := by simp [le_def]
  not_mem_empty _ := by simp
  mem_cons_iff := by simp

class IsClosed (𝓢 : Schema L) : Prop where
  closed : ∀ ω : Rew L ℕ 0 ℕ 0, ∀ φ ∈ 𝓢, ω ▹ φ ∈ 𝓢

namespace IsClosed

instance : IsClosed (⊤ : Schema L) where
  closed _ _ _ := by trivial

instance : IsClosed (⊥ : Schema L) where
  closed _ _ := by rintro ⟨⟩

instance sup (𝓢₁ 𝓢₂ : Schema L) [IsClosed 𝓢₁] [IsClosed 𝓢₂] : IsClosed (𝓢₁ ⊔ 𝓢₂) where
  closed ω φ h := by
    have : φ ∈ 𝓢₁ ∨ φ ∈ 𝓢₂ := by simpa using h
    rcases this with (h |h )
    · left; apply IsClosed.closed ω φ h
    · right; apply IsClosed.closed ω φ h

instance inf (𝓢₁ 𝓢₂ : Schema L) [IsClosed 𝓢₁] [IsClosed 𝓢₂] : IsClosed (𝓢₁ ⊓ 𝓢₂) where
  closed ω φ h := by
    have : φ ∈ 𝓢₁ ∧ φ ∈ 𝓢₂ := by simpa using h
    rcases this with ⟨h₁, h₂⟩
    constructor
    · apply IsClosed.closed ω φ h₁
    · apply IsClosed.closed ω φ h₂

lemma sSup (s : Set (Schema L)) (H : ∀ 𝓢 ∈ s, IsClosed 𝓢) : IsClosed (sSup s) where
  closed ω φ h := by
    have : ∃ 𝓢 ∈ s, φ ∈ 𝓢 := by simpa using h
    rcases this with ⟨𝓢, hs, hφ⟩
    have : IsClosed 𝓢 := H 𝓢 hs
    exact ⟨𝓢, hs, IsClosed.closed _ _ hφ⟩

instance sentence (σ : Sentence L) : IsClosed (σ : Schema L) where
  closed _ φ h := by
    have : φ = σ := by simpa using h
    rcases this
    simp

end IsClosed

def uniClosure (𝓢 : Schema L) : Theory L := Set.image Semiformula.univCl {φ | φ ∈ 𝓢}

variable {𝓢 : Schema L}

@[simp] lemma mem_uniClosure :
    σ ∈ 𝓢.uniClosure ↔ ∃ φ ∈ 𝓢, Semiformula.univCl φ = σ := by simp [uniClosure]

end Schema

end LO.FirstOrder

end

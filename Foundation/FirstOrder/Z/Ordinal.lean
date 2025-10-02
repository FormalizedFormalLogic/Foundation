import Foundation.FirstOrder.Z.Basic

/-!
# Ordinals and transitive sets in Zermelo set theory
-/

namespace LO.Zermelo

open FirstOrder SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V ⊧ₘ* 𝗭]

scoped instance : LT V := ⟨fun x y ↦ x ∈ y⟩

scoped instance : LE V := ⟨fun x y ↦ x ⊆ y⟩

omit [Nonempty V] [V ⊧ₘ* 𝗭] in
lemma lt_def {x y : V} : x < y ↔ x ∈ y := by rfl

omit [Nonempty V] [V ⊧ₘ* 𝗭] in
lemma le_def {x y : V} : x ≤ y ↔ x ⊆ y := by rfl

@[simp] lemma lt_irrefl (x : V) : ¬x < x := mem_irrefl x

omit [Nonempty V] [V ⊧ₘ* 𝗭] in
@[simp, refl] lemma le_refl (x : V) : x ≤ x := by simp [le_def]

omit [Nonempty V] [V ⊧ₘ* 𝗭] in
lemma le_trans {x y z : V} : x ≤ y → y ≤ z → x ≤ z := subset_trans

/-! ### Transitive set -/

class IsTransitive (x : V) : Prop where
  transitive : ∀ y ∈ x, y ⊆ x

omit [Nonempty V] [V ⊧ₘ* 𝗭] in
lemma isTransitive_def {x : V} : IsTransitive x ↔ ∀ y ∈ x, y ⊆ x :=
  ⟨fun h ↦ h.transitive, fun h ↦ ⟨h⟩⟩

def IsTransitive.dfn : Semisentence ℒₛₑₜ 1 := “x. ∀ y ∈ x, y ⊆ x”

instance IsTransitive.defined : ℒₛₑₜ-predicate[V] IsTransitive via IsTransitive.dfn :=
  ⟨fun v ↦ by simp [IsTransitive.dfn, isTransitive_def]⟩

instance IsTransitive.definable : ℒₛₑₜ-predicate[V] IsTransitive := IsTransitive.defined.to_definable

namespace IsTransitive

omit [Nonempty V] [V ⊧ₘ* 𝗭] in
lemma mem_trans {x y z : V} (H : IsTransitive z) (hxy : x ∈ y) (hyz : y ∈ z) : x ∈ z := H.transitive y hyz x hxy

@[simp] protected instance empty : IsTransitive (∅ : V) := ⟨fun x ↦ by simp⟩

lemma succ {x : V} (h : IsTransitive x) : IsTransitive (succ x) := ⟨by
  intro y hy
  rcases show y = x ∨ y ∈ x by simpa using hy with (rfl | hy)
  · simp
  · exact subset_trans (h.transitive y hy) (by simp)⟩

@[simp] lemma nat : x ∈ (ω : V) → IsTransitive x := by
  apply naturalNumber_induction
  · definability
  case zero =>
    simp [zero_def]
  case succ =>
    intro x hx ih
    exact ih.succ

/-
@[simp] lemma IsTransitive.ω : IsTransitive (ω : V) := by
  intro x hx
  induction x using naturalNumber_induction
  · definability
  case zero =>
    simp [zero_def]
  case succ x hx' ih =>
    intro z hz
    rcases show z = x ∨ z ∈ x by simpa using hz with (rfl | hz)
    · exact hx'
    · exact ih hx' z hz
-/

@[simp] protected instance ω : IsTransitive (ω : V) := ⟨by
  apply naturalNumber_induction
  · definability
  case zero =>
    simp [zero_def]
  case succ =>
    intro x hx ih z hz
    rcases show z = x ∨ z ∈ x by simpa using hz with (rfl | hz)
    · exact hx
    · exact ih z hz⟩

end IsTransitive

/-! ### Ordinals -/

/-- Neumann ordinal -/
class IsOrdinal (x : V) : Prop extends IsTransitive x where
  trichotomy : ∀ y ∈ x, ∀ z ∈ x, y ∈ z ∨ y = z ∨ z ∈ y

omit [Nonempty V] [V ⊧ₘ* 𝗭] in
lemma isOrdinal_iff {x : V} :
    IsOrdinal x ↔ IsTransitive x ∧ ∀ y ∈ x, ∀ z ∈ x, y ∈ z ∨ y = z ∨ z ∈ y :=
  ⟨fun h ↦ ⟨⟨h.transitive⟩, h.trichotomy⟩, fun h ↦ { transitive := h.1.transitive, trichotomy := h.2 }⟩

def IsOrdinal.dfn : Semisentence ℒₛₑₜ 1 := “x. !IsTransitive.dfn x ∧ ∀ y ∈ x, ∀ z ∈ x, y ∈ z ∨ y = z ∨ z ∈ y”

instance IsOrdinal.defined : ℒₛₑₜ-predicate[V] IsOrdinal via IsOrdinal.dfn := ⟨fun δ ↦ by simp [isOrdinal_iff, dfn]⟩

instance IsOrdinal.definable : ℒₛₑₜ-predicate[V] IsOrdinal := IsOrdinal.defined.to_definable

namespace IsOrdinal

lemma of_lt {α β : V} (h : IsOrdinal α) (lt : β < α) : IsOrdinal β where
  transitive γ hzy δ hvz := by
    have hzx : γ ∈ α := h.transitive _ lt _ hzy
    have hvx : δ ∈ α := h.transitive _ hzx _ hvz
    rcases show β ∈ δ ∨ β = δ ∨ δ ∈ β from h.trichotomy _ lt _ hvx with (hzv | rfl | hvz)
    · have : β ∉ δ := mem_asymm₃ hvz hzy
      contradiction
    · have : γ ∉ β := mem_asymm hvz
      contradiction
    · assumption
  trichotomy γ hzy δ hvy := by
    have hzx : γ ∈ α := h.transitive _ lt _ hzy
    have hvx : δ ∈ α := h.transitive _ lt _ hvy
    exact h.trichotomy γ hzx δ hvx

@[simp] protected instance empty : IsOrdinal (∅ : V) where
  trichotomy := by simp

@[simp] protected instance zero : IsOrdinal (0 : V) := .empty

protected instance succ {α : V} [h : IsOrdinal α] : IsOrdinal (succ α) where
  transitive := h.toIsTransitive.succ.transitive
  trichotomy β₁ h₁ β₂ h₂ := by
    rcases show β₁ = α ∨ β₁ ∈ α by simpa using h₁ with (rfl | h₁)
    · rcases show β₂ = β₁ ∨ β₂ ∈ β₁ by simpa using h₂ with (rfl | h₂) <;> simp_all
    · rcases show β₂ = α ∨ β₂ ∈ α by simpa using h₂ with (rfl | h₂)
      · simp_all
      · exact h.trichotomy β₁ h₁ β₂ h₂

protected instance nat : α ∈ (ω : V) → IsOrdinal (α : V) := by
  apply naturalNumber_induction
  · definability
  case zero => simp [zero_def]
  case succ => intro α hα H; exact H.succ

@[simp] instance ω : IsOrdinal (ω : V) where
  trichotomy := by sorry

end IsOrdinal

end LO.Zermelo

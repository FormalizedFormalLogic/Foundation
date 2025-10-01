import Foundation.FirstOrder.Z.Basic

/-!
# Ordinals in Zermelo set theory
-/

namespace LO.Zermelo

open FirstOrder SetTheory

variable {V : Type*} [SetStructure V] [Nonempty V] [V ⊧ₘ* 𝗭]

/-- Neumann ordinal -/
class IsOrdinal (x : V) : Prop where
  transitive : IsTransitive x
  trichotomy : ∀ y ∈ x, ∀ z ∈ x, y ∈ z ∨ y = z ∨ z ∈ y

omit [Nonempty V] [V ⊧ₘ* 𝗭] in
lemma isOrdinal_iff {x : V} :
    IsOrdinal x ↔ IsTransitive x ∧ ∀ y ∈ x, ∀ z ∈ x, y ∈ z ∨ y = z ∨ z ∈ y :=
  ⟨fun h ↦ ⟨h.transitive, h.trichotomy⟩, fun h ↦ ⟨h.1, h.2⟩⟩

def IsOrdinal.dfn : Semisentence ℒₛₑₜ 1 := “x. !IsTransitive.dfn x ∧ ∀ y ∈ x, ∀ z ∈ x, y ∈ z ∨ y = z ∨ z ∈ y”

instance IsOrdinal.defined : ℒₛₑₜ-predicate[V] IsOrdinal via IsOrdinal.dfn := ⟨fun v ↦ by simp [isOrdinal_iff, dfn]⟩

instance IsOrdinal.definable : ℒₛₑₜ-predicate[V] IsOrdinal := IsOrdinal.defined.to_definable

namespace IsOrdinal

lemma of_mem {x y : V} (h : IsOrdinal x) (mem : y ∈ x) : IsOrdinal y where
  transitive z hzy v hvz := by
    have hzx : z ∈ x := h.transitive _ mem _ hzy
    have hvx : v ∈ x := h.transitive _ hzx _ hvz
    rcases show y ∈ v ∨ y = v ∨ v ∈ y from h.trichotomy _ mem _ hvx with (hzv | rfl | hvz)
    · have : y ∉ v := mem_asymm₃ hvz hzy
      contradiction
    · have : z ∉ y := mem_asymm hvz
      contradiction
    · assumption
  trichotomy z hzy v hvy := by
    have hzx : z ∈ x := h.transitive _ mem _ hzy
    have hvx : v ∈ x := h.transitive _ mem _ hvy
    exact h.trichotomy z hzx v hvx

instance succ {α : V} [h : IsOrdinal α] : IsOrdinal (succ α) where
  transitive := h.transitive.succ
  trichotomy β₁ h₁ β₂ h₂ := by
    rcases show β₁ = α ∨ β₁ ∈ α by simpa using h₁ with (rfl | h₁)
    · rcases show β₂ = β₁ ∨ β₂ ∈ β₁ by simpa using h₂ with (rfl | h₂) <;> simp_all
    · rcases show β₂ = α ∨ β₂ ∈ α by simpa using h₂ with (rfl | h₂)
      · simp_all
      · exact h.trichotomy β₁ h₁ β₂ h₂

@[simp] instance empty : IsOrdinal (∅ : V) := ⟨by simp, by simp⟩

@[simp] instance nat (h : x ∈ (ω : V)) : IsOrdinal (x : V) where
  transitive := IsTransitive.nat h
  trichotomy := by
    revert h
    apply naturalNumber_induction
    · definability
    case zero => simp [zero_def]
    case succ =>
      intro x hx ih y hy z hz
      rcases show y = x ∨ y ∈ x by simpa using hy with (rfl | hy)
      · rcases show z = y ∨ z ∈ y by simpa using hz with (rfl | hz) <;> simp_all
      · rcases show z = x ∨ z ∈ x by simpa using hz with (rfl | hz) <;> simp_all

@[simp] instance ω : IsOrdinal (ω : V) where
  transitive := by simp
  trichotomy := by sorry

end IsOrdinal

end LO.Zermelo

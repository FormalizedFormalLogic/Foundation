module

public import Foundation.Propositional.Hilbert.Standard.Basic

@[expose] public section

/-!
  # Dialectica-like realizableation of intuitionistic propositional logic
-/

namespace LO.Propositional.Dialectica

open Formula

inductive Player
  | eloise : Player
  | abelard : Player

notation "ℰ" => Player.eloise
notation "𝒜" => Player.abelard

abbrev Argument : Player → Formula α → Type
  | ℰ,       ⊥ => Unit
  | 𝒜,       ⊥ => Unit
  | ℰ, .atom _ => Unit
  | 𝒜, .atom _ => Unit
  | ℰ,   φ ⋏ ψ => Argument ℰ φ × Argument ℰ ψ
  | 𝒜,   φ ⋏ ψ => Argument 𝒜 φ ⊕ Argument 𝒜 ψ
  | ℰ,   φ ⋎ ψ => Argument ℰ φ ⊕ Argument ℰ ψ
  | 𝒜,   φ ⋎ ψ => Argument 𝒜 φ × Argument 𝒜 ψ
  | ℰ,   φ ➝ ψ => (Argument ℰ φ → Argument ℰ ψ) × (Argument ℰ φ → Argument 𝒜 ψ → Argument 𝒜 φ)
  | 𝒜,   φ ➝ ψ => Argument ℰ φ × Argument 𝒜 ψ

abbrev Witness (φ : Formula α) := Argument ℰ φ

abbrev Counter (φ : Formula α) := Argument 𝒜 φ

abbrev Realizable (V : α → Prop) : (φ : Formula α) → Witness φ → Counter φ → Prop
  |       ⊥,      (),       () => False
  | .atom a,      (),       () => V a
  |   φ ⋏ _, ⟨θ₁, _⟩,  .inl π₁ => Realizable V φ θ₁ π₁
  |   _ ⋏ ψ, ⟨_, θ₂⟩,  .inr π₂ => Realizable V ψ θ₂ π₂
  |   φ ⋎ _, .inl θ₁, ⟨π₁,  _⟩ => Realizable V φ θ₁ π₁
  |   _ ⋎ ψ, .inr θ₂, ⟨ _, π₂⟩ => Realizable V ψ θ₂ π₂
  |   φ ➝ ψ,  ⟨f, g⟩, ⟨ θ,  π⟩ => Realizable V φ θ (g θ π) → Realizable V ψ (f θ) π

scoped notation:80 "⟦" w " | " c "⟧⊩[" V "] " φ:46 => Realizable V φ w c

def Valid (φ : Formula α) : Prop := ∃ w, ∀ V c, ⟦w | c⟧⊩[V] φ

def NotValid (φ : Formula α) : Prop := ∀ w, ∃ V c, ¬⟦w | c⟧⊩[V] φ

scoped notation "⊩ " φ => Valid φ

scoped notation "⊮ " φ => NotValid φ

lemma not_valid_iff_notValid {φ : Formula α} : (¬⊩ φ) ↔ (⊮ φ) := by
  simp [Valid, NotValid]

namespace Realizable

@[simp] lemma falsum {w c V} : ¬⟦w | c⟧⊩[V] (⊥ : Formula α) := id

@[simp] lemma atom {w c V} {a : α} : (⟦w | c⟧⊩[V] .atom a) ↔ V a := Eq.to_iff rfl

@[simp] lemma and_left {φ ψ : Formula α} {V θ π} :
    ⟦θ | .inl π⟧⊩[V] φ ⋏ ψ ↔ ⟦θ.1 | π⟧⊩[V] φ := Eq.to_iff rfl

@[simp] lemma and_right {φ ψ : Formula α} {V θ π} :
    ⟦θ | .inr π⟧⊩[V] φ ⋏ ψ ↔ ⟦θ.2 | π⟧⊩[V] ψ := Eq.to_iff rfl

@[simp] lemma or_left {φ ψ : Formula α} {V θ π} :
    ⟦.inl θ | π⟧⊩[V] φ ⋎ ψ ↔ ⟦θ | π.1⟧⊩[V] φ := Eq.to_iff rfl

@[simp] lemma or_right {φ ψ : Formula α} {V θ π} :
    ⟦.inr θ | π⟧⊩[V] φ ⋎ ψ ↔ ⟦θ | π.2⟧⊩[V] ψ := Eq.to_iff rfl

@[simp] lemma imply {φ ψ : Formula α} {V f π} :
    ⟦f | π⟧⊩[V] φ ➝ ψ ↔ (⟦π.1 | f.2 π.1 π.2⟧⊩[V] φ → ⟦f.1 π.1 | π.2⟧⊩[V] ψ) := Eq.to_iff rfl

@[simp] lemma verum {w c V} : ⟦w | c⟧⊩[V] (⊤ : Formula α) := by simp [Realizable]

@[simp] lemma not {φ : Formula α} {V θ f} : ⟦f | θ⟧⊩[V] ∼φ ↔ ¬⟦θ.1 | f.2 θ.1 θ.2⟧⊩[V] φ := Eq.to_iff rfl

end Realizable

protected lemma Valid.refl (φ : Formula α) : ⊩ φ ➝ φ := ⟨⟨id, fun _ π ↦ π⟩, by rintro V ⟨θ, π⟩; simp⟩

lemma NotValid.em (a : α) : ⊮ atom a ⋎ ∼atom a := by
  rintro (⟨⟨⟩⟩ | ⟨f⟩)
  · refine ⟨fun _ ↦ False, ⟨(), (), ()⟩, ?_⟩
    rw [Realizable.or_left]; simp
  · rcases f with ⟨f₁, f₂⟩
    have : f₁ = id := rfl
    rcases this
    have : f₂ = fun _ _ ↦ () := rfl
    rcases this
    refine ⟨fun _ ↦ true, ⟨(), (), ()⟩, ?_⟩
    rw [Realizable.or_right]; simp

end LO.Propositional.Dialectica

end

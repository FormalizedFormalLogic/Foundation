import Foundation.Propositional.Hilbert.Basic

/-!
  # A Toy Model of Dialectica Interpretation for Intuitionistic Propositional Logic

  ### References: https://math.andrej.com/2011/01/03/the-dialectica-interpertation-in-coq/

-/

namespace LO.Propositional.Dialectica

open Formula

inductive Player
  | w : Player
  | c : Player

abbrev Argument : Player → Formula α → Type
  -- | _, ⊤        => Unit
  | _, ⊥        => Unit
  | .w, .atom _ => Unit
  | .c, .atom _ => Unit
  | .w, φ ⋏ ψ   => Argument .w φ × Argument .w ψ
  | .c, φ ⋏ ψ   => Argument .c φ ⊕ Argument .c ψ
  | .w, φ ⋎ ψ   => Argument .w φ ⊕ Argument .w ψ
  | .c, φ ⋎ ψ   => Argument .c φ × Argument .c ψ
  -- | .w, ∼φ      => Argument .w φ → Argument .c φ
  -- | .c, ∼φ      => Argument .w φ
  | .w, φ ➝ ψ   => (Argument .w φ → Argument .w ψ) × (Argument .w φ → Argument .c ψ → Argument .c φ)
  | .c, φ ➝ ψ   => Argument .w φ × Argument .c ψ

abbrev Witness (φ : Formula α) := Argument .w φ

abbrev Counter (φ : Formula α) := Argument .c φ

def Interpret (V : α → Prop) : (φ : Formula α) → Witness φ → Counter φ → Prop
  --| ⊤,       (),       ()      => True
  | ⊥,       (),       ()      => False
  | .atom a, (),       ()      => V a
  | φ ⋏ _,   ⟨θ₁, _⟩,  .inl π₁ => Interpret V φ θ₁ π₁
  | _ ⋏ ψ,   ⟨_, θ₂⟩,  .inr π₂ => Interpret V ψ θ₂ π₂
  | φ ⋎ _,   .inl θ₁,  ⟨π₁, _⟩ => Interpret V φ θ₁ π₁
  | _ ⋎ ψ,   .inr θ₂,  ⟨_, π₂⟩ => Interpret V ψ θ₂ π₂
  -- | ∼φ,      f,        θ       => ¬Interpret V φ θ (f θ)
  | φ ➝ ψ,   ⟨f, g⟩,   ⟨θ, π⟩  => Interpret V φ θ (g θ π) → Interpret V ψ (f θ) π

scoped notation:80 "⟦" w " | " c "⟧⊩[" V "] " φ:46 => Interpret V φ w c

def Valid (φ : Formula α) : Prop := ∃ w, ∀ V c, ⟦w | c⟧⊩[V] φ

def NotValid (φ : Formula α) : Prop := ∀ w, ∃ V c, ¬⟦w | c⟧⊩[V] φ

scoped notation "⊩ " φ => Valid φ

scoped notation "⊮ " φ => NotValid φ

lemma not_valid_iff_notValid {φ : Formula α} : (¬⊩ φ) ↔ (⊮ φ) := by
  simp [Valid, NotValid]

@[simp] lemma interpret_falsum {w c V} : ¬⟦w | c⟧⊩[V] (⊥ : Formula α) := id

@[simp] lemma interpret_atom {w c V} {a : α} : (⟦w | c⟧⊩[V] .atom a) ↔ V a := Eq.to_iff rfl

@[simp] lemma interpret_K!_left {φ ψ : Formula α} {V θ π} :
    ⟦θ | .inl π⟧⊩[V] φ ⋏ ψ ↔ ⟦θ.1 | π⟧⊩[V] φ := Eq.to_iff rfl

@[simp] lemma interpret_K!_right {φ ψ : Formula α} {V θ π} :
    ⟦θ | .inr π⟧⊩[V] φ ⋏ ψ ↔ ⟦θ.2 | π⟧⊩[V] ψ := Eq.to_iff rfl

@[simp] lemma interpret_or_left {φ ψ : Formula α} {V θ π} :
    ⟦.inl θ | π⟧⊩[V] φ ⋎ ψ ↔ ⟦θ | π.1⟧⊩[V] φ := Eq.to_iff rfl

@[simp] lemma interpret_or_right {φ ψ : Formula α} {V θ π} :
    ⟦.inr θ | π⟧⊩[V] φ ⋎ ψ ↔ ⟦θ | π.2⟧⊩[V] ψ := Eq.to_iff rfl

@[simp] lemma interpret_imply {φ ψ : Formula α} {V f π} :
    ⟦f | π⟧⊩[V] φ ➝ ψ ↔ (⟦π.1 | f.2 π.1 π.2⟧⊩[V] φ → ⟦f.1 π.1 | π.2⟧⊩[V] ψ) := Eq.to_iff rfl

@[simp] lemma interpret_verum {w c V} : ⟦w | c⟧⊩[V] (⊤ : Formula α) := by simp

@[simp] lemma interpret_not {φ : Formula α} {V θ f} : ⟦f | θ⟧⊩[V] ∼φ ↔ ¬⟦θ | f θ⟧⊩[V] φ := Eq.to_iff rfl

protected lemma Valid.refl (φ : Formula α) : ⊩ φ ➝ φ := ⟨⟨id, fun _ π ↦ π⟩, by rintro V ⟨θ, π⟩; simp⟩

lemma NotValid.em (a : α) : ⊮ atom a ⋎ ∼atom a := by
  rintro (⟨⟨⟩⟩ | ⟨f⟩)
  · refine ⟨fun _ ↦ False, ⟨(), ()⟩, ?_⟩
    rw [interpret_or_left]; simp
  · have : f = id := rfl
    rcases this
    refine ⟨fun _ ↦ true, ⟨(), ()⟩, ?_⟩
    rw [interpret_or_right]; simp

end LO.Propositional.Dialectica

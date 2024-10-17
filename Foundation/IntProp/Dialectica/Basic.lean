import Foundation.IntProp.Deduction

/-!
  # A Toy Model of Dialectica Interpretation for Intuitionistic Propositional Logic

  ### References: https://math.andrej.com/2011/01/03/the-dialectica-interpertation-in-coq/

-/

namespace LO.IntProp.Dialectica

open Formula

inductive Player
  | w : Player
  | c : Player

abbrev Argument : Player → Formula α → Type
  | _, ⊤        => Unit
  | _, ⊥        => Unit
  | .w, .atom _ => Unit
  | .c, .atom _ => Unit
  | .w, p ⋏ q   => Argument .w p × Argument .w q
  | .c, p ⋏ q   => Argument .c p ⊕ Argument .c q
  | .w, p ⋎ q   => Argument .w p ⊕ Argument .w q
  | .c, p ⋎ q   => Argument .c p × Argument .c q
  | .w, ∼p      => Argument .w p → Argument .c p
  | .c, ∼p      => Argument .w p
  | .w, p ➝ q   => (Argument .w p → Argument .w q) × (Argument .w p → Argument .c q → Argument .c p)
  | .c, p ➝ q   => Argument .w p × Argument .c q

abbrev Witness (p : Formula α) := Argument .w p

abbrev Counter (p : Formula α) := Argument .c p

def Interpret (V : α → Prop) : (p : Formula α) → Witness p → Counter p → Prop
  | ⊤,       (),       ()      => True
  | ⊥,       (),       ()      => False
  | .atom a, (),       ()      => V a
  | p ⋏ _,   ⟨θ₁, _⟩,  .inl π₁ => Interpret V p θ₁ π₁
  | _ ⋏ q,   ⟨_, θ₂⟩,  .inr π₂ => Interpret V q θ₂ π₂
  | p ⋎ _,   .inl θ₁,  ⟨π₁, _⟩ => Interpret V p θ₁ π₁
  | _ ⋎ q,   .inr θ₂,  ⟨_, π₂⟩ => Interpret V q θ₂ π₂
  | ∼p,      f,        θ       => ¬Interpret V p θ (f θ)
  | p ➝ q,   ⟨f, g⟩,   ⟨θ, π⟩  => Interpret V p θ (g θ π) → Interpret V q (f θ) π

scoped notation "⟦" w " | " c "⟧ ⊩[" V "] " p:46 => Interpret V p w c

def Valid (p : Formula α) : Prop := ∃ w, ∀ V c, ⟦w | c⟧ ⊩[V] p

def NotValid (p : Formula α) : Prop := ∀ w, ∃ V c, ¬⟦w | c⟧ ⊩[V] p

scoped notation "⊩ " p => Valid p

scoped notation "⊮ " p => NotValid p

lemma not_valid_iff_notValid {p : Formula α} : (¬⊩ p) ↔ (⊮ p) := by
  simp [Valid, NotValid]

@[simp] lemma interpret_verum {w c V} : ⟦w | c⟧ ⊩[V] (⊤ : Formula α) := trivial

@[simp] lemma interpret_falsum {w c V} : ¬⟦w | c⟧ ⊩[V] (⊥ : Formula α) := id

@[simp] lemma interpret_atom {w c V} {a : α} : (⟦w | c⟧ ⊩[V] .atom a) ↔ V a := Eq.to_iff rfl

@[simp] lemma interpret_and_left {p q : Formula α} {V θ π} :
    ⟦θ | .inl π⟧ ⊩[V] p ⋏ q ↔ ⟦θ.1 | π⟧ ⊩[V] p := Eq.to_iff rfl

@[simp] lemma interpret_and_right {p q : Formula α} {V θ π} :
    ⟦θ | .inr π⟧ ⊩[V] p ⋏ q ↔ ⟦θ.2 | π⟧ ⊩[V] q := Eq.to_iff rfl

@[simp] lemma interpret_or_left {p q : Formula α} {V θ π} :
    ⟦.inl θ | π⟧ ⊩[V] p ⋎ q ↔ ⟦θ | π.1⟧ ⊩[V] p := Eq.to_iff rfl

@[simp] lemma interpret_or_right {p q : Formula α} {V θ π} :
    ⟦.inr θ | π⟧ ⊩[V] p ⋎ q ↔ ⟦θ | π.2⟧ ⊩[V] q := Eq.to_iff rfl

@[simp] lemma interpret_not {p : Formula α} {V θ f} :
    ⟦f | θ⟧ ⊩[V] ∼p ↔ ¬⟦θ | f θ⟧ ⊩[V] p := Eq.to_iff rfl

@[simp] lemma interpret_imply {p q : Formula α} {V f π} :
    ⟦f | π⟧ ⊩[V] p ➝ q ↔ (⟦π.1 | f.2 π.1 π.2⟧ ⊩[V] p → ⟦f.1 π.1 | π.2⟧ ⊩[V] q) := Eq.to_iff rfl

protected lemma Valid.refl (p : Formula α) : ⊩ p ➝ p := ⟨⟨id, fun _ π ↦ π⟩, by rintro V ⟨θ, π⟩; simp⟩

lemma NotValid.em (a : α) : ⊮ atom a ⋎ ∼atom a := by
  rintro (⟨⟨⟩⟩ | ⟨f⟩)
  · refine ⟨fun _ ↦ False, ⟨(), ()⟩, ?_⟩
    rw [interpret_or_left]; simp
  · have : f = id := rfl
    rcases this
    refine ⟨fun _ ↦ true, ⟨(), ()⟩, ?_⟩
    rw [interpret_or_right]; simp

end LO.IntProp.Dialectica

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
  | .c, .atom _ => Bool
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

def Interpret : (p : Formula α) → Witness p → Counter p → Prop
  | ⊤,       (),       ()       => True
  | ⊥,       (),       ()       => False
  | .atom _, (),       b        => b
  | p ⋏ _,   ⟨θ₁, _⟩,  .inl π₁  => Interpret p θ₁ π₁
  | _ ⋏ q,   ⟨_, θ₂⟩,  .inr π₂  => Interpret q θ₂ π₂
  | p ⋎ _,   .inl θ₁,  ⟨π₁, _⟩  => Interpret p θ₁ π₁
  | _ ⋎ q,   .inr θ₂,  ⟨_, π₂⟩  => Interpret q θ₂ π₂
  | ∼p,      f,        π        => ¬Interpret p π (f π)
  | p ➝ q,   ⟨f, g⟩,   ⟨π₁, π₂⟩ => Interpret p π₁ (g π₁ π₂) → Interpret q (f π₁) π₂

notation "⟦" w " | " c "⟧ ⊩ " p:46 => Interpret p w c

def Valid (p : Formula α) : Prop := ∃ w, ∀ c, ⟦w | c⟧ ⊩ p

notation "⊩ " p => Valid p

@[simp] lemma interpret_verum {w c} : ⟦w | c⟧ ⊩ (⊤ : Formula α) := trivial

@[simp] lemma interpret_falsum {w c} : ¬⟦w | c⟧ ⊩ (⊥ : Formula α) := id

@[simp] lemma interpret_atom {w c} {a : α} : (⟦w | c⟧ ⊩ .atom a) ↔ c := Eq.to_iff rfl

@[simp] lemma interpret_and_left {p q : Formula α} {θ π} :
    ⟦θ | .inl π⟧ ⊩ p ⋏ q ↔ ⟦θ.1 | π⟧ ⊩ p := Eq.to_iff rfl

@[simp] lemma interpret_and_right {p q : Formula α} {θ π} :
    ⟦θ | .inr π⟧ ⊩ p ⋏ q ↔ ⟦θ.2 | π⟧ ⊩ q := Eq.to_iff rfl

@[simp] lemma interpret_or_left {p q : Formula α} {θ π} :
    ⟦.inl θ | π⟧ ⊩ p ⋎ q ↔ ⟦θ | π.1⟧ ⊩ p := Eq.to_iff rfl

@[simp] lemma interpret_or_right {p q : Formula α} {θ π} :
    ⟦.inr θ | π⟧ ⊩ p ⋎ q ↔ ⟦θ | π.2⟧ ⊩ q := Eq.to_iff rfl

@[simp] lemma interpret_not {p : Formula α} {f π} :
    ⟦f | π⟧ ⊩ ∼p ↔ ¬⟦π | f π⟧ ⊩ p := Eq.to_iff rfl

@[simp] lemma interpret_imply {p q : Formula α} {f π} :
    ⟦f | π⟧ ⊩ p ➝ q ↔ (⟦π.1 | f.2 π.1 π.2⟧ ⊩ p → ⟦f.1 π.1 | π.2⟧ ⊩ q) := Eq.to_iff rfl

lemma atom_id (a : α) : ⊩ atom a ➝ atom a := ⟨⟨id, fun _ π ↦ π⟩, by rintro ⟨⟨⟩, π⟩; simp⟩

end LO.IntProp.Dialectica

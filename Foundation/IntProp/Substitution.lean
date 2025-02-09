import Foundation.IntProp.Formula

namespace LO.IntProp

abbrev Substitution (α) := α → (Formula α)

abbrev Substitution.id {α} : Substitution α := λ a => .atom a

namespace Formula

variable {φ ψ : Formula α} {s : Substitution α}

def subst (s : Substitution α) : Formula α → Formula α
  | atom a  => (s a)
  | ⊥       => ⊥
  | φ ⋏ ψ   => φ.subst s ⋏ ψ.subst s
  | φ ⋎ ψ   => φ.subst s ⋎ ψ.subst s
  | φ ➝ ψ   => φ.subst s ➝ ψ.subst s

notation:80 φ "⟦" s "⟧" => Formula.subst s φ

@[simp] lemma subst_atom {a} : (.atom a)⟦s⟧ = s a := rfl

@[simp] lemma subst_bot : ⊥⟦s⟧ = ⊥ := rfl

@[simp] lemma subst_top : ⊤⟦s⟧ = ⊤ := rfl

@[simp] lemma subst_imp : (φ ➝ ψ)⟦s⟧ = φ⟦s⟧ ➝ ψ⟦s⟧ := rfl

@[simp] lemma subst_neg : (∼φ)⟦s⟧ = ∼(φ⟦s⟧) := rfl

@[simp] lemma subst_and : (φ ⋏ ψ)⟦s⟧ = φ⟦s⟧ ⋏ ψ⟦s⟧ := rfl

@[simp] lemma subst_or : (φ ⋎ ψ)⟦s⟧ = φ⟦s⟧ ⋎ ψ⟦s⟧ := rfl

@[simp] lemma subst_iff : (φ ⭤ ψ)⟦s⟧ = (φ⟦s⟧ ⭤ ψ⟦s⟧) := rfl

end Formula


@[simp] lemma subst_id {φ : Formula α} : φ⟦.id⟧ = φ := by induction φ using Formula.rec' <;> simp_all;

def Substitution.comp (s₁ s₂ : Substitution α) : Substitution α := λ a => (s₁ a)⟦s₂⟧
infixr:80 " ∘ " => Substitution.comp

@[simp]
lemma subst_comp {s₁ s₂ : Substitution α} {φ : Formula α} : φ⟦s₁ ∘ s₂⟧ = φ⟦s₁⟧⟦s₂⟧ := by
  induction φ using Formula.rec' <;> simp_all [Substitution.comp];

class SubstitutionClosed (S : Set (Formula α)) where
  closed : ∀ φ ∈ S, (∀ s : Substitution α, φ⟦s⟧ ∈ S)


end LO.IntProp

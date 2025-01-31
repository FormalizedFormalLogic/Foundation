import Foundation.Modal.Formula

namespace LO.Modal

abbrev Substitution (α) := α → (Formula α)

abbrev Substitution.id {α} : Substitution α := λ a => .atom a

namespace Formula

variable {φ ψ : Formula α} {s : Substitution α}

def subst (s : Substitution α) : Formula α → Formula α
  | atom a  => (s a)
  | ⊥       => ⊥
  | □φ      => □(φ.subst s)
  | φ ➝ ψ   => φ.subst s ➝ ψ.subst s

notation:80 φ "⟦" s "⟧" => Formula.subst s φ

@[simp] lemma subst_atom {a} : (.atom a)⟦s⟧ = s a := rfl

@[simp] lemma subst_bot : ⊥⟦s⟧ = ⊥ := rfl

@[simp] lemma subst_imp : (φ ➝ ψ)⟦s⟧ = φ⟦s⟧ ➝ ψ⟦s⟧ := rfl

@[simp] lemma subst_neg : (∼φ)⟦s⟧ = ∼(φ⟦s⟧) := rfl

@[simp] lemma subst_and : (φ ⋏ ψ)⟦s⟧ = φ⟦s⟧ ⋏ ψ⟦s⟧ := rfl

@[simp] lemma subst_or : (φ ⋎ ψ)⟦s⟧ = φ⟦s⟧ ⋎ ψ⟦s⟧ := rfl

@[simp] lemma subst_iff : (φ ⭤ ψ)⟦s⟧ = (φ⟦s⟧ ⭤ ψ⟦s⟧) := rfl

@[simp] lemma subst_box : (□φ)⟦s⟧ = □(φ⟦s⟧) := rfl

@[simp] lemma subst_dia : (◇φ)⟦s⟧ = ◇(φ⟦s⟧) := rfl

end Formula


@[simp] lemma subst_id {φ : Formula α} : φ⟦.id⟧ = φ := by induction φ using Formula.rec' <;> simp_all;


class SubstitutionClosed (S : Set (Formula α)) where
  closed : ∀ φ ∈ S, (∀ s : Substitution α, φ⟦s⟧ ∈ S)


end LO.Modal

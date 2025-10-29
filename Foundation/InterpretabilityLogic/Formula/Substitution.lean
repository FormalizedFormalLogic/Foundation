import Foundation.InterpretabilityLogic.Formula.Basic
import Foundation.Modal.Formula

namespace LO.InterpretabilityLogic

variable {α : Type*}

abbrev Substitution (α) := α → Formula α

@[grind]
def Formula.subst (s : Substitution α) : Formula α → Formula α
  | atom a => s a
  | ⊥      => ⊥
  | φ ➝ ψ  => (φ.subst s) ➝ (ψ.subst s)
  | □φ     => □(φ.subst s)
  | φ ▷ ψ  => (φ.subst s) ▷ (ψ.subst s)

notation φ "⟦" s "⟧" => Formula.subst s φ

namespace Formula

variable {s : Substitution α} {φ ψ : Formula α}

lemma subst_atom {a : α} : (.atom a)⟦s⟧ = s a := rfl
lemma subst_falsum : ⊥⟦s⟧ = ⊥ := rfl
lemma subst_verum : ⊤⟦s⟧ = ⊤ := rfl
lemma subst_neg : (∼φ)⟦s⟧ = ∼(φ⟦s⟧) := rfl
lemma subst_imp : (φ ➝ ψ)⟦s⟧ = (φ⟦s⟧) ➝ (ψ⟦s⟧) := rfl
lemma subst_and : (φ ⋏ ψ)⟦s⟧ = (φ⟦s⟧) ⋏ (ψ⟦s⟧) := rfl
lemma subst_or : (φ ⋎ ψ)⟦s⟧ = (φ⟦s⟧) ⋎ (ψ⟦s⟧) := rfl
lemma subst_box : (□φ)⟦s⟧ = □(φ⟦s⟧) := rfl
lemma subst_dia : (◇φ)⟦s⟧ = ◇(φ⟦s⟧) := rfl
lemma subst_rhd : (φ ▷ ψ)⟦s⟧ = (φ⟦s⟧) ▷ (ψ⟦s⟧) := rfl

attribute [simp, grind]
  subst_atom
  subst_falsum
  subst_verum
  subst_neg
  subst_imp
  subst_and
  subst_or
  subst_box
  subst_dia
  subst_rhd

end Formula

abbrev idSubstitution (α) : Substitution α := Formula.atom

@[simp] lemma Formula.subst_id : φ⟦idSubstitution α⟧ = φ := by induction φ <;> simp [Formula.subst, *]


def Substitution.comp (s₁ s₂ : Substitution α) : Substitution α := λ a => (s₁ a)⟦s₂⟧
infixr:80 " ∘ " => Substitution.comp

@[simp, grind]
lemma Formula.comp_subst {s₁ s₂ : Substitution α} {φ : Formula α} : φ⟦s₁ ∘ s₂⟧ = φ⟦s₁⟧⟦s₂⟧ := by
  induction φ <;> simp_all [Substitution.comp];


end LO.InterpretabilityLogic

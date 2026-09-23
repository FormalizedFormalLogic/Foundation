module

public import Foundation.ProvabilityLogic.Formula.Basic

/-!
# Substitution
-/

@[expose] public section

namespace FFL.ProvabilityLogic

namespace Formula

variable {α β : Type*}

abbrev Substitution (α β : Type*) := α → Formula β

@[grind]
def subst (s : Substitution α β) : Formula α → Formula β
  | #a    => s a
  | ⊥     => ⊥
  | A 🡒 B => A.subst s 🡒 B.subst s
  | □A    => □(A.subst s)

scoped notation:80 A "⟦" s "⟧" => Formula.subst s A

variable {s : Substitution α β} {A B : Formula α}

@[simp, grind =] lemma subst_atom {a : α} : (#a)⟦s⟧ = s a := rfl
@[simp, grind =] lemma subst_bot : (⊥ : Formula α)⟦s⟧ = ⊥ := rfl
@[simp, grind =] lemma subst_top : (⊤ : Formula α)⟦s⟧ = ⊤ := rfl
@[simp, grind =] lemma subst_imp : (A 🡒 B)⟦s⟧ = A⟦s⟧ 🡒 B⟦s⟧ := rfl
@[simp, grind =] lemma subst_neg : (∼A)⟦s⟧ = ∼A⟦s⟧ := rfl
@[simp, grind =] lemma subst_and : (A ⋏ B)⟦s⟧ = A⟦s⟧ ⋏ B⟦s⟧ := rfl
@[simp, grind =] lemma subst_or : (A ⋎ B)⟦s⟧ = A⟦s⟧ ⋎ B⟦s⟧ := rfl
@[simp, grind =] lemma subst_box : (□A)⟦s⟧ = □A⟦s⟧ := rfl
@[simp, grind =] lemma subst_dia : (◇A)⟦s⟧ = ◇A⟦s⟧ := rfl

@[simp, grind =]
lemma subst_boxItr {n : ℕ} : (□^[n]A)⟦s⟧ = □^[n]A⟦s⟧ := by
  induction n <;> simp_all;

end Formula

end FFL.ProvabilityLogic

end

import Foundation.Modal.Formula.Basic.Basic
import Foundation.Propositional.ClassicalSemantics.ZeroSubst


namespace LO

namespace Propositional

def Formula.toModalFormula : Propositional.Formula α → Modal.Formula α
  | .atom a => Modal.Formula.atom a
  | ⊥ => ⊥
  | φ ➝ ψ => (toModalFormula φ) ➝ (toModalFormula ψ)
  | φ ⋏ ψ => (toModalFormula φ) ⋏ (toModalFormula ψ)
  | φ ⋎ ψ => (toModalFormula φ) ⋎ (toModalFormula ψ)

namespace Formula.toModalFormula

instance : Coe (Propositional.Formula α) (Modal.Formula α) := ⟨Formula.toModalFormula⟩

variable {α} {a : α} {φ ψ : Propositional.Formula α}

@[simp] protected lemma def_atom : toModalFormula (.atom a) = .atom a := by rfl
@[simp] protected lemma def_top : toModalFormula (⊤ : Propositional.Formula α) = ⊤ := by rfl
@[simp] protected lemma def_bot : toModalFormula (⊥ : Propositional.Formula α) = ⊥ := by rfl
@[simp] protected lemma def_not : toModalFormula (∼φ) = ∼(φ.toModalFormula) := by rfl
@[simp] protected lemma def_imp : toModalFormula (φ ➝ ψ) = (φ.toModalFormula) ➝ (ψ.toModalFormula) := by rfl
@[simp] protected lemma def_and : toModalFormula (φ ⋏ ψ) = (φ.toModalFormula) ⋏ (ψ.toModalFormula) := by rfl
@[simp] protected lemma def_or : toModalFormula (φ ⋎ ψ) = (φ.toModalFormula) ⋎ (ψ.toModalFormula) := by rfl

end Formula.toModalFormula

end Propositional


namespace Modal

def Formula.toPropFormula (φ : Modal.Formula α) (_ : φ.degree = 0 := by grind) : Propositional.Formula α :=
  match φ with
  | atom a => Propositional.Formula.atom a
  | ⊥ => ⊥
  | φ ➝ ψ => φ.toPropFormula ➝ ψ.toPropFormula

abbrev PropositionalFormula (α) := { φ : Modal.Formula α // φ.degree = 0 }

instance : Coe (PropositionalFormula α) (Propositional.Formula α) := ⟨fun ⟨φ, hφ⟩ => φ.toPropFormula hφ⟩

end Modal

end LO

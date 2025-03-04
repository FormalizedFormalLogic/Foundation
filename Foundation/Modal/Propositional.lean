import Foundation.Propositional.Formula
import Foundation.Modal.Formula

namespace LO.Propositional

def Formula.toModalFormula : Formula α → Modal.Formula α
  | .atom a => Modal.Formula.atom a
  | ⊥ => ⊥
  | φ ➝ ψ => (toModalFormula φ) ➝ (toModalFormula ψ)
  | φ ⋏ ψ => (toModalFormula φ) ⋏ (toModalFormula ψ)
  | φ ⋎ ψ => (toModalFormula φ) ⋎ (toModalFormula ψ)

namespace Formula.toModalFormula

instance : Coe (Formula α) (Modal.Formula α) := ⟨Formula.toModalFormula⟩

variable {α} {φ ψ : Formula α}

@[simp] lemma def_top : toModalFormula (⊤ : Formula α) = ⊤ := by rfl

@[simp] lemma def_bot : toModalFormula (⊥ : Formula α) = ⊥ := by rfl

@[simp] lemma def_atom : toModalFormula (atom a) = .atom a := by rfl

@[simp] lemma def_not : toModalFormula (∼φ) = ∼(φ.toModalFormula) := by rfl

@[simp] lemma def_imp : toModalFormula (φ ➝ ψ) = (φ.toModalFormula) ➝ (ψ.toModalFormula) := by rfl

@[simp] lemma def_and : toModalFormula (φ ⋏ ψ) = (φ.toModalFormula) ⋏ (ψ.toModalFormula) := by rfl

@[simp] lemma def_or : toModalFormula (φ ⋎ ψ) = (φ.toModalFormula) ⋎ (ψ.toModalFormula) := by rfl

end Formula.toModalFormula

end LO.Propositional


namespace LO.Modal

def Formula.toPropFormula (φ : Formula α) (_ : φ.degree = 0 := by simp_all [Formula.degree, Formula.degree_neg, Formula.degree_imp]) : Propositional.Formula α :=
  match φ with
  | atom a => Propositional.Formula.atom a
  | ⊥ => ⊥
  | φ ➝ ψ => φ.toPropFormula ➝ ψ.toPropFormula

abbrev PropositionalFormula (α) := { φ : Formula α // φ.degree = 0 }

instance : Coe (PropositionalFormula α) (Propositional.Formula α) := ⟨fun ⟨φ, hφ⟩ => φ.toPropFormula hφ⟩

end LO.Modal

import Foundation.IntProp.Formula
import Foundation.Modal.Formula

namespace LO.IntProp

def Formula.toModalFormula : Formula α → Modal.Formula α
  | .atom a => Modal.Formula.atom a
  | ⊥ => ⊥
  | φ ➝ ψ => (toModalFormula φ) ➝ (toModalFormula ψ)
  | φ ⋏ ψ => (toModalFormula φ) ⋏ (toModalFormula ψ)
  | φ ⋎ ψ => (toModalFormula φ) ⋎ (toModalFormula ψ)
postfix:75 "ᴹ" => Formula.toModalFormula

namespace Formula.toModalFormula

@[simp] lemma def_top : (⊤ : Formula α)ᴹ = ⊤ := by rfl

@[simp] lemma def_bot : (⊥ : Formula α)ᴹ = ⊥ := by rfl

@[simp] lemma def_atom (a : α) : (atom a)ᴹ = .atom a := by rfl

@[simp] lemma def_not (φ : Formula α) : (∼φ)ᴹ = ∼(φᴹ) := by rfl

@[simp] lemma def_imp (φ ψ : Formula α) : (φ ➝ ψ)ᴹ = (φᴹ) ➝ (ψᴹ) := by rfl

@[simp] lemma def_and (φ ψ : Formula α) : (φ ⋏ ψ)ᴹ = (φᴹ) ⋏ (ψᴹ) := by rfl

@[simp] lemma def_or (φ ψ : Formula α) : (φ ⋎ ψ)ᴹ = (φᴹ) ⋎ (ψᴹ) := by rfl

end Formula.toModalFormula

end LO.IntProp


namespace LO.Modal

def Formula.toPropFormula (φ : Formula α) (_ : φ.degree = 0 := by simp_all [Formula.degree, Formula.degree_neg, Formula.degree_imp]) : IntProp.Formula α :=
  match φ with
  | atom a => IntProp.Formula.atom a
  | ⊥ => ⊥
  | φ ➝ ψ => φ.toPropFormula ➝ ψ.toPropFormula
postfix:75 "ᴾ" => Formula.toPropFormula

end LO.Modal

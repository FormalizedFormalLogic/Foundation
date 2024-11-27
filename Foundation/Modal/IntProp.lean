import Foundation.IntProp.Kripke.Classical
import Foundation.Modal.Formula

namespace LO.IntProp

def Formula.toModalFormula : Formula α → Modal.Formula α
  | .atom a => Modal.Formula.atom a
  | ⊤ => ⊤
  | ⊥ => ⊥
  | ∼φ => ∼(toModalFormula φ)
  | φ ➝ ψ => (toModalFormula φ) ➝ (toModalFormula ψ)
  | φ ⋏ ψ => (toModalFormula φ) ⋏ (toModalFormula ψ)
  | φ ⋎ ψ => (toModalFormula φ) ⋎ (toModalFormula ψ)
postfix:75 "ᴹ" => Formula.toModalFormula

end LO.IntProp


namespace LO.Modal

def Formula.toPropFormula (φ : Formula α) (_ : φ.degree = 0 := by simp_all [Formula.degree, Formula.degree_neg, Formula.degree_imp]) : IntProp.Formula α :=
  match φ with
  | atom a => IntProp.Formula.atom a
  | ⊥ => ⊥
  | φ ➝ ψ => φ.toPropFormula ➝ ψ.toPropFormula
postfix:75 "ᴾ" => Formula.toPropFormula

end LO.Modal

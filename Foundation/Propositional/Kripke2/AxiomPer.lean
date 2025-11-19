import Foundation.Propositional.Kripke2.Basic
import Foundation.Vorspiel.HRel.Convergent
import Foundation.Vorspiel.HRel.Euclidean
import Foundation.Vorspiel.HRel.Coreflexive

namespace LO.Propositional

namespace Axioms

variable {F : Type*} [LogicalConnective F]
variable (φ ψ χ : F)

/-- Axioms of persistency -/
protected abbrev Per := φ ➝ ⊤ ➝ φ

end Axioms


open Kripke2
open Formula.Kripke2

namespace Kripke2

variable {M : Kripke2.Model} {φ ψ χ : Formula ℕ}


namespace Model

protected class IsPersistent (M : Kripke2.Model) where
  persistent : ∀ {a x y}, M x a → x ≺ y → M y a
export IsPersistent (persistent)

end Model


@[simp high, grind .]
lemma valid_axiomRfl_of_isReflexive {a} [M.IsPersistent] : M ⊧ Axioms.Per #a := by
  intro x y Rxy h z Ryz _;
  apply M.persistent h Ryz;

lemma isPersistent_of_valid_axiomPer (h : ∀ a, M ⊧ Axioms.Per #a) : M.IsPersistent := by
  constructor;
  intro a x y h₁ Rxy;
  apply h a M.root M.rooted h₁ Rxy;
  tauto;

end Kripke2

end LO.Propositional

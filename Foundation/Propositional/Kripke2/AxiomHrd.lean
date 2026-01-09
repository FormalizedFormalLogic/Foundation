module
import Foundation.Propositional.Kripke2.Basic
import Foundation.Vorspiel.Rel.Convergent
import Foundation.Vorspiel.Rel.Euclidean
import Foundation.Vorspiel.Rel.Coreflexive

namespace LO.Propositional

open Kripke2
open Formula.Kripke2

namespace Kripke2

variable {M : Kripke2.Model} {φ ψ χ : Formula ℕ}


namespace Model

protected class IsHereditary (M : Kripke2.Model) where
  hereditary : ∀ {a x y}, M x a → x ≺ y → M y a
export IsHereditary (hereditary)

end Model


@[simp high, grind .]
lemma valid_axiomHrd_of_isHereditary {a} [M.IsHereditary] : M ⊧ Axioms.Hrd #a := by
  intro x y Rxy h z Ryz _;
  apply M.hereditary h Ryz;

lemma isHereditary_of_valid_axiomHrd (h : ∀ a, M ⊧ Axioms.Hrd #a) : M.IsHereditary := by
  constructor;
  intro a x y h₁ Rxy;
  apply h a M.root M.rooted h₁ Rxy;
  tauto;

end Kripke2

end LO.Propositional

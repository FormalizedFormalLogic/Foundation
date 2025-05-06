import Foundation.Propositional.Formula

namespace LO.Propositional

namespace Axioms

protected abbrev BoundDepth' : ℕ → Formula ℕ
  | 0     => (.atom 0) ⋎ ∼(.atom 0)
  | n + 1 => (.atom (n + 1)) ⋎ ((.atom (n + 1)) ➝ Axioms.BoundDepth' n)

protected abbrev BoundDepth (n : ℕ+) : Formula ℕ := Axioms.BoundDepth' n.natPred

end Axioms

end LO.Propositional

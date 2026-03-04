module

public import Foundation.FirstOrder.Incompleteness.RosserProvability

@[expose] public section
/-!
# Gödel-Rosser Incompleteness Theorem.
-/

namespace LO.FirstOrder.Arithmetic

open LO.Entailment ProvabilityAbstraction

/-- Gödel-Rosser incompleteness theorem -/
theorem incomplete' (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [Consistent T] : Entailment.Incomplete T :=
  rosser_first_incompleteness T.rosserProvability

end LO.FirstOrder.Arithmetic

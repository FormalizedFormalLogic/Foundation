import Foundation.FirstOrder.Bootstrapping.RosserProvability

/-!
# Gödel-Rosser Incompleteness Theorem.
-/

namespace LO.FirstOrder.Arithmetic

open LO.Entailment ProvabilityLogic

/-- Gödel-Rosser incompleteness theorem -/
theorem incomplete' (T : Theory ℒₒᵣ) [T.Δ₁] [𝗜𝚺₁ ⪯ T] [Consistent T] : Entailment.Incomplete T :=
  T.rosserProvability.rosser_first_incompleteness

end LO.FirstOrder.Arithmetic

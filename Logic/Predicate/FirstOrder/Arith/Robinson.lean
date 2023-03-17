import Logic.Predicate.FirstOrder.Eq

namespace FirstOrder

namespace Arith

variable {L : Language.{u}} [L.HasORing]

inductive Robinson : CTheory L
  | q₁ : Robinson “∀ 0 ≠ #0 + 1”
  | q₂ : Robinson “∀ ∀ (#1 + 1 = #0 + 1 → #1 = #0)”
  | q₃ : Robinson “∀ (#0 = 0 ∨ (∃ #1 = #0 + 1))”
  | q₄ : Robinson “∀ #0 + 0 = #0”
  | q₅ : Robinson “∀ ∀ (#1 + (#0 + 1) = (#1 + #0) + 1)”
  | q₆ : Robinson “∀ #0 * 0 = 0”
  | q₇ : Robinson “∀ ∀ (#1 * (#0 + 1) = #1 * #0 + #1)”
  | q₈ : Robinson “∀ ∀ (#1 < #0 ↔ (∃ #0 + #2 + 1 = #1))”

end Arith

end FirstOrder
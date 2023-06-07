import Logic.Predicate.FirstOrder.Eq
import Logic.Predicate.FirstOrder.Arith.Hierarchy

namespace FirstOrder

variable {L : Language.{u}} [L.ORing]

namespace Arith

def succInd (p : SubFormula L μ 1) : Formula L μ := “!p⟦0⟧ → ∀ (!p⟦#0⟧ → !p⟦#0 + 1⟧) → ∀ !p”

def leastNumber (p : SubFormula L μ 1) : Formula L μ := “∃ !p → ∃ (!p ∧ ∀[#0 < #1] ¬!p⟦#0⟧)”

def orderInd (p : SubFormula L μ 1) : Formula L μ := “∀ (∀[#0 < #1] !p⟦#0⟧ → !p⟦#0⟧) → ∀ !p”

end Arith

namespace Theory

namespace Arith

variable (L)

inductive Robinson : Theory L
  | q₁ : Robinson “∀ #0 + 1 ≠ 0”
  | q₂ : Robinson “∀ ∀ (#0 + 1 = #1 + 1 → #0 = #1)”
  | q₃ : Robinson “∀ (#0 = 0 ∨ (∃ #1 = #0 + 1))”
  | q₄ : Robinson “∀ #0 + 0 = #0”
  | q₅ : Robinson “∀ ∀ (#0 + (#1 + 1) = (#0 + #1) + 1)”
  | q₆ : Robinson “∀ #0 * 0 = 0”
  | q₇ : Robinson “∀ ∀ (#0 * (#1 + 1) = #0 * #1 + #0)”
  | q₈ : Robinson “∀ ∀ (#0 < #1 ↔ (∃ #0 + #1 + 1 = #2))”

inductive PAminus : Theory L
  | addZero       : PAminus “∀ #0 + 0 = #0”
  | addAssoc      : PAminus “∀ ∀ ∀ (#0 + #1) + #2 = #0 + (#1 + #2)”
  | addComm       : PAminus “∀ ∀ #0 + #1 = #1 + #0”
  | ltDef         : PAminus “∀ ∀ (#0 < #1 ↔ (∃ #0 + #1 + 1 = #2))”
  | zeroBot       : PAminus “∀ 0 ≤ #0”
  | zeroLeOne     : PAminus “0 < 1”
  | oneLeOfZeroLt : PAminus “∀ (0 < #0 → 1 ≤ #0)”
  | addLtAdd      : PAminus “∀ ∀ ∀ (#0 < #1 → #0 + #2 < #1 + #2)”
  | mulZero       : PAminus “∀ #0 * 0 = 0”
  | mulOne        : PAminus “∀ #0 * 1 = #0”
  | mulAssoc      : PAminus “∀ ∀ ∀ (#0 * #1) * #2 = #0 * (#1 + #2)”
  | mulComm       : PAminus “∀ ∀ #0 * #1 = #1 * #0”
  | mulLtMul      : PAminus “∀ ∀ ∀ (#0 < #1 → #2 ≠ 0 → #0 * #2 < #1 * #2)”
  | distr         : PAminus “∀ ∀ ∀ #0 * (#1 + #2) = #0 * #1 + #0 * #2”

inductive Ind (U : Set (SubSentence L 1)) : Theory L
  | intro {σ} : σ ∈ U → Ind U (Arith.succInd σ) 

section Paring
variable [L.Pairing]

inductive Pairing : Sentence L → Prop
  | pairing : Pairing “∀ ∀ ∀ (⟨#0, #1⟩ = #2 ↔ (#0 + #1 + 1) * (#0 + #1) + 2 * #0 = 2 * #2)”

end Paring

section Exp
variable [L.Exp]

inductive Exp : Theory L
  | zero : Exp “exp 0 = 1”
  | succ : Exp “∀ exp (#0 + 1) = exp #0 * 2”

end Exp

end Arith

class RobinsonTheory (T : Theory L) extends EqTheory T where
  robinson : Arith.Robinson L ⊆ T

class IndTheory (U) (T : Theory L) extends RobinsonTheory T where
  ind : Arith.Ind L U ⊆ T

abbrev IOpen (T : Theory L) := IndTheory SubFormula.qfree T

abbrev ISigma (k : ℕ) (T : Theory L) := IndTheory (Arith.Hierarchy.Sigma k) T

abbrev IPi (k : ℕ) (T : Theory L) := IndTheory (Arith.Hierarchy.Pi k) T

abbrev Peano (T : Theory L) := IndTheory Set.univ T

abbrev PairingTheory [L.Pairing] (T : Theory L) := SubTheory (Arith.Pairing L) T

end Theory

end FirstOrder
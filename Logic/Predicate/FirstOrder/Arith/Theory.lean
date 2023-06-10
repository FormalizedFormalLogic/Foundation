import Logic.Predicate.FirstOrder.Order.Le
import Logic.Predicate.FirstOrder.Arith.Hierarchy

namespace FirstOrder

variable {L : Language.{u}} [L.ORing]

namespace Arith

def succInd (p : SubFormula L μ (k + 1)) : Formula L μ :=
  “∀* (!(⟦→ ᵀ“0” :> (#·)⟧ p) → ∀ (!(⟦→ ᵀ“#0” :> (#·.succ)⟧ p) → !(⟦→ ᵀ“#0 + 1” :> (#·.succ)⟧ p)) → ∀ !p)”

def leastNumber (p : SubFormula L μ (k + 1)) : Formula L μ :=
  “∀* (∃ !p → ∃ (!p ∧ ∀[#0 < #1] ¬!(⟦→ #0 :> (#·.succ.succ)⟧ p)))”

def orderInd (p : SubFormula L μ (k + 1)) : Formula L μ :=
  “∀* (∀ (∀[#0 < #1] !(⟦→ #0 :> (#·.succ.succ)⟧ p) → !p) → ∀ !p)”

variable (L)

namespace Theory

inductive Robinson : Theory L
  | q₁ : Robinson “∀ #0 + 1 ≠ 0”
  | q₂ : Robinson “∀ ∀ (#0 + 1 = #1 + 1 → #0 = #1)”
  | q₃ : Robinson “∀ (#0 = 0 ∨ (∃ #1 = #0 + 1))”
  | q₄ : Robinson “∀ #0 + 0 = #0”
  | q₅ : Robinson “∀ ∀ (#0 + (#1 + 1) = (#0 + #1) + 1)”
  | q₆ : Robinson “∀ #0 * 0 = 0”
  | q₇ : Robinson “∀ ∀ (#0 * (#1 + 1) = #0 * #1 + #0)”
  | q₈ : Robinson “∀ ∀ (#0 ≤ #1 ↔ (∃ #0 + #1 = #2))”

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

variable {L}

def IndScheme (u : Set (SubSentence L 1)) : Theory L := succInd '' u

variable (L)

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

end Theory

variable {L}

class Robinson (T : Theory L) where
  robinson : Theory.Robinson L ⊆ T

attribute [simp] Robinson.robinson

class Ind (U) (T : Theory L) where
  ind : Theory.IndScheme U ⊆ T

attribute [simp] Ind.ind

abbrev IOpen (T : Theory L) := Ind SubFormula.qfree T

abbrev ISigma (k : ℕ) (T : Theory L) := Ind (Arith.Hierarchy.Sigma k) T

abbrev IPi (k : ℕ) (T : Theory L) := Ind (Arith.Hierarchy.Pi k) T

abbrev Peano (T : Theory L) := Ind Set.univ T

abbrev PairingTheory [L.Pairing] (T : Theory L) := SubTheory (Theory.Pairing L) T

namespace Axiom

variable (L)

def Robinson : Theory L := Theory.Robinson L ∪ Theory.Eq L

variable {L}

def Ind (U : Set (SubSentence L 1)) : Theory L := Axiom.Robinson L ∪ Theory.IndScheme U

variable (L)

abbrev IOpen : Theory L := Ind SubFormula.qfree

abbrev ISigma (k : ℕ) : Theory L := Ind (Arith.Hierarchy.Sigma k)

abbrev IPi (k : ℕ) : Theory L := Ind (Arith.Hierarchy.Pi k)

abbrev Peano : Theory L := Ind Set.univ

instance : EqTheory (Robinson L) where
  eq := by simp[Robinson]

instance : Arith.Robinson (Robinson L) where
  robinson := by simp[Robinson]

instance (u : Set (SubSentence L 1)) : EqTheory (Ind u) where
  eq := by simp[Ind]; exact Set.subset_union_of_subset_left (by simp) _

instance (u : Set (SubSentence L 1)) : Arith.Robinson (Ind u) where
  robinson := by simp[Ind]; exact Set.subset_union_of_subset_left (by simp) _

instance (u : Set (SubSentence L 1)) : Arith.Ind u (Ind u) where
  ind := by simp[Ind]

end Axiom

end Arith

end FirstOrder
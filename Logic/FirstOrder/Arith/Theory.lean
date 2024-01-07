import Logic.FirstOrder.Arith.Hierarchy

namespace LO

namespace FirstOrder

variable {L : Language} [L.ORing]

abbrev Formula.univClosure {n} (p : Formula L (Fin n)) : Sentence L := ∀* (Rew.toS.hom p)

prefix:64 "∀ᵤ* " => Formula.univClosure

namespace Arith


def succInd {ξ} (p : Semiformula L ξ 1) : Formula L ξ := “!p [0] → ∀ (!p [#0] → !p [#0 + 1]) → ∀ !p [#0]”

def orderInd {ξ} (p : Semiformula L ξ 1) : Formula L ξ := “∀ (∀[#0 < #1] !p [#0] → !p [#0]) → ∀ !p [#0]”

def leastNumber {ξ} (p : Semiformula L ξ 1) : Formula L ξ := “∃ !p [#0] → ∃ (!p [#0] ∧ ∀[#0 < #1] ¬!p [#0])”

def succIndᵤ {n} (p : Semiformula L (Fin n) 1) : Sentence L := ∀ᵤ* succInd p

variable (L)

namespace Theory

inductive PAminus : Theory L
  | addZero       : PAminus “∀ #0 + 0 = #0”
  | addAssoc      : PAminus “∀ ∀ ∀ (#2 + #1) + #0 = #2 + (#1 + #0)”
  | addComm       : PAminus “∀ ∀ #1 + #0 = #0 + #1”
  | addEqOfLt     : PAminus “∀ ∀ (#1 < #0 → ∃ #2 + #0 = #1)”
  | zeroLe        : PAminus “∀ (0 ≤ #0)”
  | zeroLtOne     : PAminus “0 < 1”
  | oneLeOfZeroLt : PAminus “∀ (0 < #0 → 1 ≤ #0)”
  | addLtAdd      : PAminus “∀ ∀ ∀ (#2 < #1 → #2 + #0 < #1 + #0)”
  | mulZero       : PAminus “∀ #0 * 0 = 0”
  | mulOne        : PAminus “∀ #0 * 1 = #0”
  | mulAssoc      : PAminus “∀ ∀ ∀ (#2 * #1) * #0 = #2 * (#1 * #0)”
  | mulComm       : PAminus “∀ ∀ #1 * #0 = #0 * #1”
  | mulLtMul      : PAminus “∀ ∀ ∀ (#2 < #1 ∧ 0 < #0 → #2 * #0 < #1 * #0)”
  | distr         : PAminus “∀ ∀ ∀ #2 * (#1 + #0) = #2 * #1 + #2 * #0”
  | ltIrrefl      : PAminus “∀ ¬#0 < #0”
  | ltTrans       : PAminus “∀ ∀ ∀ (#2 < #1 ∧ #1 < #0 → #2 < #0)”
  | ltTri         : PAminus “∀ ∀ (#1 < #0 ∨ #1 = #0 ∨ #0 < #1)”

notation "𝐏𝐀⁻" => PAminus ℒₒᵣ

variable {L}

def IndScheme (u : {n : ℕ} → Set (Semiformula L (Fin n) 1)) : Theory L := { ∀ᵤ* succInd p | (n : ℕ) (p ∈ @u n) }

variable (L)

abbrev IndSchemeOpen : Theory L := IndScheme Semiformula.qfree

notation "𝐈open" => IndSchemeOpen ℒₒᵣ

abbrev IndSchemeSigma (k : ℕ) : Theory L := IndScheme (Arith.Hierarchy Σ k)

prefix:max "𝐈𝚺" => IndSchemeSigma ℒₒᵣ

abbrev Peano : Theory L := IndScheme Set.univ

notation "𝐏𝐀" => Peano ℒₒᵣ

end Theory

end Arith

end FirstOrder

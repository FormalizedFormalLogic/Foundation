import Logic.FirstOrder.Arith.Hierarchy

namespace LO

namespace FirstOrder

variable {L : Language} [L.ORing]

namespace Arith

def succInd (p : Semiformula L μ (k + 1)) : Formula L μ :=
  “∀* (!((Rew.substs (ᵀ“0” :> (#·))).hom p) → ∀ (!((Rew.substs  (ᵀ“#0” :> (#·.succ))).hom p) →
   !((Rew.substs (ᵀ“#0 + 1” :> (#·.succ))).hom p)) → ∀ !p)”

def succInd' (p : Semiformula.Operator L (k + 1)) : Formula L μ :=
  “∀* (!(p.operator (ᵀ“0” :> (#·))) →
       ∀ (!(p.operator (#0 :> (#·.succ))) → !(p.operator (ᵀ“#0 + 1” :> (#·.succ)))) →
       ∀ !(p.operator (#0 :> (#·.succ))))”

def leastNumber (p : Semiformula L μ (k + 1)) : Formula L μ :=
  “∀* (∃ !p → ∃ (!p ∧ ∀[#0 < #1] ¬!((Rew.substs (#0 :> (#·.succ.succ))).hom p)))”

def orderInd (p : Semiformula L μ (k + 1)) : Formula L μ :=
  “∀* (∀ (∀[#0 < #1] !((Rew.substs (#0 :> (#·.succ.succ))).hom p) → !p) → ∀ !p)”

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

def IndScheme (u : Set (Semisentence L 1)) : Theory L := succInd '' u

variable (L)

abbrev IndSchemeOpen : Theory L := IndScheme Semiformula.qfree

notation "𝐈open" => IndSchemeOpen ℒₒᵣ

abbrev IndSchemeDelta (k : ℕ) : Theory L := IndScheme (Arith.Hierarchy Σ k)

prefix:max "𝐈Δ" => IndSchemeDelta ℒₒᵣ

abbrev Peano : Theory L := IndScheme Set.univ

notation "𝐏𝐀" => Peano ℒₒᵣ

end Theory

end Arith

end FirstOrder

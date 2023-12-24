import Logic.FirstOrder.Arith.Hierarchy

namespace LO

namespace FirstOrder

variable {L : Language} [FirstOrder.ORing L]

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

variable {L}

def IndScheme (u : Set (Semisentence L 1)) : Theory L := succInd '' u

variable (L)

end Theory

variable {L}

abbrev PAminus (T : Theory L) := System.Subtheory (Theory.PAminus L) T

abbrev Ind (U) (T : Theory L) := System.Subtheory (Theory.IndScheme U) T

abbrev IOpen (T : Theory L) := Ind Semiformula.qfree T

abbrev IDelta (k : ℕ) (T : Theory L) := Ind (Arith.Hierarchy.Sigma k) T

abbrev Peano (T : Theory L) := Ind Set.univ T

namespace Axiom

variable (L)

def paminus : Theory L := Theory.Eq L ∪ Theory.PAminus L

variable {L}

def ind (U : Set (Semisentence L 1)) : Theory L := Axiom.paminus L ∪ Theory.IndScheme U

variable (L)

abbrev iopen : Theory L := ind Semiformula.qfree

abbrev idelta (k : ℕ) : Theory L := ind (Arith.Hierarchy.Sigma k)

abbrev peano : Theory L := ind Set.univ

instance : EqTheory (paminus L) where
  eq := by simp[paminus]

instance : Arith.PAminus (paminus L) := System.Subtheory.ofSubset _ _ (by simp[paminus])

instance (u : Set (Semisentence L 1)) : EqTheory (ind u) where
  eq := by simp[ind]; exact Set.subset_union_of_subset_left (by simp) _

instance (u : Set (Semisentence L 1)) : Arith.PAminus (ind u) :=
  System.Subtheory.ofSubset _ _ (by simp[ind, paminus]; exact Set.subset_union_of_subset_left (by simp) _)

instance (u : Set (Semisentence L 1)) : Arith.Ind u (ind u) := System.Subtheory.ofSubset _ _ (by simp[ind])

notation "𝐏𝐀⁻" => paminus ℒₒᵣ

notation "𝐈open" => iopen ℒₒᵣ

prefix:max "𝐈Δ" => idelta ℒₒᵣ

notation "𝐏𝐀" => peano ℒₒᵣ

end Axiom

end Arith

end FirstOrder

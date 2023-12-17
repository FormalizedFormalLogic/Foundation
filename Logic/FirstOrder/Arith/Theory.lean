import Logic.FirstOrder.Arith.Hierarchy

namespace LO

namespace FirstOrder

variable {L : Language.{u}} [FirstOrder.ORing L]
  [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)]


namespace Arith

def succInd (p : Subformula L μ (k + 1)) : Formula L μ :=
  “∀* (!((Rew.substs (ᵀ“0” :> (#·))).hom p) → ∀ (!((Rew.substs  (ᵀ“#0” :> (#·.succ))).hom p) →
   !((Rew.substs (ᵀ“#0 + 1” :> (#·.succ))).hom p)) → ∀ !p)”

def succInd' (p : Subformula.Operator L (k + 1)) : Formula L μ :=
  “∀* (!(p.operator (ᵀ“0” :> (#·))) →
       ∀ (!(p.operator (#0 :> (#·.succ))) → !(p.operator (ᵀ“#0 + 1” :> (#·.succ)))) →
       ∀ !(p.operator (#0 :> (#·.succ))))”

def leastNumber (p : Subformula L μ (k + 1)) : Formula L μ :=
  “∀* (∃ !p → ∃ (!p ∧ ∀[#0 < #1] ¬!((Rew.substs (#0 :> (#·.succ.succ))).hom p)))”

def orderInd (p : Subformula L μ (k + 1)) : Formula L μ :=
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

def IndScheme (u : Set (Subsentence L 1)) : Theory L := succInd '' u

variable (L)

end Theory

variable {L}

abbrev PAminus (T : Theory L) := System.Subtheory (Theory.PAminus L) T

abbrev Ind (U) (T : Theory L) := System.Subtheory (Theory.IndScheme U) T

abbrev IOpen (T : Theory L) := Ind Subformula.qfree T

abbrev IDelta (k : ℕ) (T : Theory L) := Ind (Arith.Hierarchy.Sigma k) T

abbrev Peano (T : Theory L) := Ind Set.univ T

/-
namespace Axiom

variable (L)

def PAminus : Theory L := Theory.PAminus L ∪ Theory.Eq L

variable {L}

def Ind (U : Set (Subsentence L 1)) : Theory L := Axiom.PAminus L ∪ Theory.IndScheme U

variable (L)

abbrev IOpen : Theory L := Ind Subformula.qfree

abbrev ISigma (k : ℕ) : Theory L := Ind (Arith.Hierarchy.Sigma k)

abbrev IPi (k : ℕ) : Theory L := Ind (Arith.Hierarchy.Pi k)

abbrev Peano : Theory L := Ind Set.univ

instance : EqTheory (PAminus L) where
  eq := by simp[PAminus]

instance : Arith.PAminus (PAminus L) := System.Subtheory.ofSubset _ _ (by simp[PAminus])

instance (u : Set (Subsentence L 1)) : EqTheory (Ind u) where
  eq := by simp[Ind]; exact Set.subset_union_of_subset_left (by simp) _

instance (u : Set (Subsentence L 1)) : Arith.PAminus (Ind u) :=
  System.Subtheory.ofSubset _ _ (by simp[Ind, PAminus]; exact Set.subset_union_of_subset_left (by simp) _)

instance (u : Set (Subsentence L 1)) : Arith.Ind u (Ind u) := System.Subtheory.ofSubset _ _ (by simp[Ind])

end Axiom
-/

end Arith

end FirstOrder

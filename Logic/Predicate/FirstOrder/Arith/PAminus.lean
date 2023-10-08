import Logic.Predicate.FirstOrder.Arith.Theory
import Logic.Predicate.FirstOrder.Principia.Meta

namespace LO

namespace FirstOrder
variable {L : Language.{u}} [L.ORing] [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]
variable {T : Theory L} [EqTheory T] [Arith.PAminus T]

namespace Arith

namespace PAminus

def addZero : [] ⟹[T] “∀ #0 + 0 = #0” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.addZero)

def addAssoc : [] ⟹[T] “∀ ∀ ∀ (#0 + #1) + #2 = #0 + (#1 + #2)” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.addAssoc)

def addComm : [] ⟹[T] “∀ ∀ #0 + #1 = #1 + #0” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.addComm)

def addEqOfLt : [] ⟹[T] “∀ ∀ (#0 < #1 → ∃ #1 + #0 = #2)” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.addEqOfLt)

def zeroLe : [] ⟹[T] “∀ (0 ≤ #0)” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.zeroLe)

def zeroLtOne : [] ⟹[T] “0 < 1” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.zeroLtOne)

def oneLeOfZeroLt : [] ⟹[T] “∀ (0 < #0 → 1 ≤ #0)” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.oneLeOfZeroLt)

def addLtAdd : [] ⟹[T] “∀ ∀ ∀ (#0 < #1 → #0 + #2 < #1 + #2)” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.addLtAdd)

def mulZero : [] ⟹[T] “∀ #0 * 0 = 0” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.mulZero)

def mulOne : [] ⟹[T] “∀ #0 * 1 = #0” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.mulOne)

def mulAssoc : [] ⟹[T] “∀ ∀ ∀ (#0 * #1) * #2 = #0 * (#1 * #2)” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.mulAssoc)

def mulComm : [] ⟹[T] “∀ ∀ #0 * #1 = #1 * #0” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.mulComm)

def mulLtMul : [] ⟹[T] “∀ ∀ ∀ (#0 < #1 ∧ 0 < #2 → #0 * #2 < #1 * #2)” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.mulLtMul)

def distr : [] ⟹[T] “∀ ∀ ∀ #0 * (#1 + #2) = #0 * #1 + #0 * #2” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.distr)

def leIffEqOrLt : [] ⟹[T] “∀ ∀ (#0 ≤ #1 ↔ #0 = #1 ∨ #0 < #1)” :=
  by simp[SubFormula.le_eq]; exact proofBy { gens _ _; refl }

def ltIrrefl : [] ⟹[T] “∀ ¬#0 < #0” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.ltIrrefl)

def ltTrans : [] ⟹[T] “∀ ∀ ∀ (#0 < #1 ∧ #1 < #2 → #0 < #2)” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.ltTrans)

def ltTri : [] ⟹[T] “∀ ∀ (#0 < #1 ∨ #0 = #1 ∨ #1 < #0)” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.ltTri)

def ltOfLeOfLt : [] ⟹[T] “∀ ∀ ∀ (#0 ≤ #1 ∧ #1 < #2 → #0 < #2)” :=
  proof.
    then (lt_iff) “∀ ∀ (#0 ≤ #1 ↔ #0 = #1 ∨ #0 < #1)” · from leIffEqOrLt
    then (lt_trans) “∀ ∀ ∀ (#0 < #1 ∧ #1 < #2 → #0 < #2)” · from ltTrans
    gens n m l; intro h
    have “l = m ∨ l < m”
    · specialize lt_iff with l, m
      rw[←this]
      andl h
    cases (hl) “l = m” or (hl) “l < m”
    · rw[this]
      andr h
    · specialize lt_trans with l, m, n
      apply this
      · split
        @ assumption
        @ andr h
  qed.

def leOfLt : [] ⟹[T] “∀ ∀ (#0 < #1 → #0 ≤ #1)” :=
  proof.
    gens n m; intro h
    then “∀ ∀ (#0 ≤ #1 ↔ #0 = #1 ∨ #0 < #1)” · from leIffEqOrLt
    specialize this with m, n
    rw[this]
    right
  qed.

def leRefl : [] ⟹[T] “∀ #0 ≤ #0” :=
  proof.
    gen n
    then “∀ ∀ (#0 ≤ #1 ↔ #0 = #1 ∨ #0 < #1)” · from leIffEqOrLt
    specialize this with n, n
    rw[this]
    left; refl
  qed.

def zeroAdd : [] ⟹[T] “∀ 0 + #0 = #0” :=
proof.
  then (add_zero) “∀ #0 + 0 = #0” · from addZero
  then (add_comm) “∀ ∀ #0 + #1 = #1 + #0” · from addComm
  gen n
  specialize add_zero with n
  specialize add_comm with 0, n
  rw[this]
qed.

/-
def leAdd : [] ⟹[T] “∀ ∀ #0 ≤ #0 + #1” :=
  proof.
    gen n; gen m
    have 0 = n ∨ 0 < n
    · specialize 0 ≤ #0 with n @ efrom zeroLe
      specialize #0 ≤ #1 ↔ #0 = #1 ∨ #0 < #1 with 0, n @ efrom leIffEqOrLt
      rw[←this]
    cases 0 = n as .hn or 0 < n as .hn
    · specialize #0 ≤ #0 with m @ efrom leRefl
      specialize #0 + 0 = #0 with m @ efrom addZero
      rw[←.hn, this]
    · have m < m + n
      · specialize 0 + #0 = #0 with m @ efrom zeroAdd
        ?
        then ∀ ∀ ∀ (#0 < #1 → #0 + #2 < #1 + #2) as .add_lt_add · from addLtAdd
        specialize this with 0, n, m

  qed.

def numeralLtSucc {n m : ℕ} (h : n < m) : [] ⟹[T] “∀ ∀ #0 < #0 + 1 + #1” :=
  proof.
    gen n; gen m
    
    ?
  qed.
-/

def numeralAdd (n m : ℕ) : [] ⟹[T] “ᵀ!(SubTerm.natLit L n) + ᵀ!(SubTerm.natLit L m) = ᵀ!(SubTerm.natLit L (n + m))” := by
  induction' m with m ih
  · simp
    exact proofBy {
      then “∀ #0 + 0 = #0” · from addZero
      specialize this with ᵀ!(SubTerm.Operator.const $ SubTerm.natLit L n) }
  · by_cases hm : m = 0
    · simp[hm, Nat.add_succ] at ih ⊢
      suffices : [] ⟹[T] “ᵀ!(SubTerm.natLit L n) + 1 = ᵀ!(SubTerm.natLit L (n + 1))”
      { exact this.cast (by rfl) }
      by_cases hn : n = 0
      · simp[hn]
        exact proofBy {
          then “∀ 0 + #0 = #0” · from zeroAdd
          specialize this with 1 }
      · simp[hn, SubTerm.natLit_succ]; exact proofBy { refl }
    · simp[hm, Nat.add_succ, SubTerm.natLit_succ]
      exact proof.
        then (ih) “ᵀ!(SubTerm.natLit L n) + ᵀ!(SubTerm.natLit L m) = ᵀ!(SubTerm.natLit L (n + m))” · from ih
        then (add_succ) “∀ ∀ ∀ (#0 + #1) + #2 = #0 + (#1 + #2)” · from addAssoc
        specialize this with ᵀ!(SubTerm.Operator.const $ SubTerm.natLit L n), ᵀ!(SubTerm.Operator.const $ SubTerm.natLit L m), 1
        rw[←this, ih]
        refl
      qed.
      
def numeralMul (n m : ℕ) : [] ⟹[T] “ᵀ!(SubTerm.natLit L n) * ᵀ!(SubTerm.natLit L m) = ᵀ!(SubTerm.natLit L (n * m))” := by
  induction' m with m ih
  · simp
    exact proofBy {
      then “∀ #0 * 0 = 0” · from mulZero
      specialize this with ᵀ!(SubTerm.Operator.const $ SubTerm.natLit L n) }
  · by_cases hm : m = 0
    · simp[hm, Nat.add_succ] at ih ⊢
      suffices : [] ⟹[T] “ᵀ!(SubTerm.natLit L n) * 1 = ᵀ!(SubTerm.natLit L n)”
      { exact this.cast (by rfl) }
      exact proofBy {
        then “∀ #0 * 1 = #0” · from mulOne
        specialize this with ᵀ!(SubTerm.Operator.const $ SubTerm.natLit L n) }
    · simp[hm, Nat.mul_succ, SubTerm.natLit_succ]
      exact proofBy {
        then “ᵀ!(SubTerm.natLit L (n * m)) + ᵀ!(SubTerm.natLit L n) = ᵀ!(SubTerm.natLit L (n * m + n))” · from numeralAdd _ _
        then (ih) “ᵀ!(SubTerm.natLit L n) * ᵀ!(SubTerm.natLit L m) = ᵀ!(SubTerm.natLit L (n * m))” · from ih
        then “∀ #0 * 1 = #0” · from mulOne
        specialize (h) this with ᵀ!(SubTerm.Operator.const $ SubTerm.natLit L n)
        then “∀ ∀ ∀ #0 * (#1 + #2) = #0 * #1 + #0 * #2” · from distr
        specialize this with ᵀ!(SubTerm.Operator.const $ SubTerm.natLit L n), ᵀ!(SubTerm.Operator.const $ SubTerm.natLit L m), 1
        rw[this, h, ih] }

def numeralLt {n m : ℕ} (h : n < m) : [] ⟹[T] “ᵀ!(SubTerm.natLit L n) < ᵀ!(SubTerm.natLit L m)” := sorry
  
def numeralNEq {n m : ℕ} (h : n ≠ m) : [] ⟹[T] “ᵀ!(SubTerm.natLit L n) ≠ ᵀ!(SubTerm.natLit L m)” := sorry

end PAminus

end Arith
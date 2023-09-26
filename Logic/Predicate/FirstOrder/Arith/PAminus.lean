import Logic.Predicate.FirstOrder.Arith.Theory
import Logic.Predicate.FirstOrder.Principia.Meta

namespace LO

namespace FirstOrder
variable {L : Language.{u}} [L.ORing] [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]
variable {T : Theory L} [EqTheory T] [Arith.PAminus T]

namespace Arith

namespace PAminus

def addZeroPR : [] ⟹[T] “∀ #0 + 0 = #0” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.addZero)

noncomputable def addZero : T ⊢ “∀ #0 + 0 = #0” := Principia.toProof (by simpa using addZeroPR)

def addAssocPR : [] ⟹[T] “∀ ∀ ∀ (#0 + #1) + #2 = #0 + (#1 + #2)” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.addAssoc)

noncomputable def addAssoc : T ⊢ “∀ ∀ ∀ (#0 + #1) + #2 = #0 + (#1 + #2)” :=
  Principia.toProof (by simpa using addAssocPR)

def addCommPR : [] ⟹[T] “∀ ∀ #0 + #1 = #1 + #0” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.addComm)

noncomputable def addComm : T ⊢ “∀ ∀ #0 + #1 = #1 + #0” :=
  Principia.toProof (by simpa using addCommPR)

def addEqOfLtPR : [] ⟹[T] “∀ ∀ (#0 < #1 → ∃ #1 + #0 = #2)” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.addEqOfLt)

noncomputable def addEqOfLt : T ⊢ “∀ ∀ (#0 < #1 → ∃ #1 + #0 = #2)” :=
  Principia.toProof (by simpa using addEqOfLtPR)

def zeroLePR : [] ⟹[T] “∀ (0 ≤ #0)” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.zeroLe)

noncomputable def zeroLe : T ⊢ “∀ (0 ≤ #0)” :=
  Principia.toProof (by simpa using zeroLePR)

def zeroLtOnePR : [] ⟹[T] “0 < 1” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.zeroLtOne)

noncomputable def zeroLtOne : T ⊢ “0 < 1” :=
  Principia.toProof (by simpa using zeroLtOnePR)

def oneLeOfZeroLtPR : [] ⟹[T] “∀ (0 < #0 → 1 ≤ #0)” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.oneLeOfZeroLt)

noncomputable def oneLeOfZeroLt : T ⊢ “∀ (0 < #0 → 1 ≤ #0)” :=
  Principia.toProof (by simpa using oneLeOfZeroLtPR)

def addLtAddPR : [] ⟹[T] “∀ ∀ ∀ (#0 < #1 → #0 + #2 < #1 + #2)” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.addLtAdd)

noncomputable def addLtAdd : T ⊢ “∀ ∀ ∀ (#0 < #1 → #0 + #2 < #1 + #2)” :=
  Principia.toProof (by simpa using addLtAddPR)

def mulZeroPR : [] ⟹[T] “∀ #0 * 0 = 0” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.mulZero)

noncomputable def mulZero : T ⊢ “∀ #0 * 0 = 0” :=
  Principia.toProof (by simpa using mulZeroPR)

def mulOnePR : [] ⟹[T] “∀ #0 * 1 = #0” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.mulOne)

noncomputable def mulOne : T ⊢ “∀ #0 * 1 = #0” :=
  Principia.toProof (by simpa using mulOnePR)

def mulAssocPR : [] ⟹[T] “∀ ∀ ∀ (#0 * #1) * #2 = #0 * (#1 * #2)” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.mulAssoc)

noncomputable def mulAssoc : T ⊢ “∀ ∀ ∀ (#0 * #1) * #2 = #0 * (#1 * #2)” :=
  Principia.toProof (by simpa using mulAssocPR)

def mulCommPR : [] ⟹[T] “∀ ∀ #0 * #1 = #1 * #0” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.mulComm)

noncomputable def mulComm : T ⊢ “∀ ∀ #0 * #1 = #1 * #0” :=
  Principia.toProof (by simpa using mulCommPR)

def mulLtMulPR : [] ⟹[T] “∀ ∀ ∀ (#0 < #1 ∧ 0 < #2 → #0 * #2 < #1 * #2)” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.mulLtMul)

noncomputable def mulLtMul : T ⊢ “∀ ∀ ∀ (#0 < #1 ∧ 0 < #2 → #0 * #2 < #1 * #2)” :=
  Principia.toProof (by simpa using mulLtMulPR)

def distrPR : [] ⟹[T] “∀ ∀ ∀ #0 * (#1 + #2) = #0 * #1 + #0 * #2” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.distr)

noncomputable def distr : T ⊢ “∀ ∀ ∀ #0 * (#1 + #2) = #0 * #1 + #0 * #2” :=
  Principia.toProof (by simpa using distrPR)

def leIffEqOrLt : [] ⟹[T] “∀ ∀ (#0 ≤ #1 ↔ #0 = #1 ∨ #0 < #1)” :=
  by simp[SubFormula.le_eq]; exact proofBy { generalize x; generalize x; refl }

def ltIrreflPR : [] ⟹[T] “∀ ¬#0 < #0” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.ltIrrefl)

noncomputable def ltIrrefl : T ⊢ “∀ ¬#0 < #0” :=
  Principia.toProof (by simpa using ltIrreflPR)

def ltTransPR : [] ⟹[T] “∀ ∀ ∀ (#0 < #1 ∧ #1 < #2 → #0 < #2)” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.ltTrans)

noncomputable def ltTrans : T ⊢ “∀ ∀ ∀ (#0 < #1 ∧ #1 < #2 → #0 < #2)” :=
  Principia.toProof (by simpa using ltTransPR)

def ltTriPR : [] ⟹[T] “∀ ∀ (#0 < #1 ∨ #0 = #1 ∨ #1 < #0)” :=
  Principia.axmOfEq _ (by simp) (Arith.PAminus.paminus $ Theory.PAminus.ltTri)

noncomputable def ltTri : T ⊢ “∀ ∀ (#0 < #1 ∨ #0 = #1 ∨ #1 < #0)” :=
  Principia.toProof (by simpa using ltTriPR)

def ltOfLeOfLt : [] ⟹[T] “∀ ∀ ∀ (#0 ≤ #1 ∧ #1 < #2 → #0 < #2)” :=
  proof.
    then ∀ ∀ (#0 ≤ #1 ↔ #0 = #1 ∨ #0 < #1) as .le_iff · from leIffEqOrLt
    then ∀ ∀ ∀ (#0 < #1 ∧ #1 < #2 → #0 < #2) as .lt_trans · from ltTransPR
    generalize n
    generalize m
    generalize l
    intro as .h
    have l = m ∨ l < m
    · specialize .le_iff with l, m
      rw[←this]
      andl .h
    cases l = m as .hl or l < m as .hl
    · rw[this]
      andr .h
    · specialize .lt_trans with l, m, n
      apply this
      · split
        @ assumption
        @ andr .h
  qed.

def leOfLt : [] ⟹[T] “∀ ∀ (#0 < #1 → #0 ≤ #1)” :=
  proof.
    generalize n; generalize m; intro as .h
    then ∀ ∀ (#0 ≤ #1 ↔ #0 = #1 ∨ #0 < #1) · from leIffEqOrLt
    specialize this with m, n
    rw[this]
    right
  qed.

def leRefl : [] ⟹[T] “∀ #0 ≤ #0” :=
  proof.
    generalize n
    then ∀ ∀ (#0 ≤ #1 ↔ #0 = #1 ∨ #0 < #1) · from leIffEqOrLt
    specialize this with n, n
    rw[this]
    left; refl
  qed.

def zeroAdd : [] ⟹[T] “∀ 0 + #0 = #0” :=
proof.
  then ∀ #0 + 0 = #0 as .add_zero · from addZeroPR
  then ∀ ∀ #0 + #1 = #1 + #0 as .add_comm · from addCommPR
  generalize n
  specialize .add_zero with n
  specialize .add_comm with 0, n
  rw[this]
qed.

/-
def leAdd : [] ⟹[T] “∀ ∀ #0 ≤ #0 + #1” :=
  proof.
    generalize n; generalize m
    have 0 = n ∨ 0 < n
    · specialize 0 ≤ #0 with n @ efrom zeroLePR
      specialize #0 ≤ #1 ↔ #0 = #1 ∨ #0 < #1 with 0, n @ efrom leIffEqOrLt
      rw[←this]
    cases 0 = n as .hn or 0 < n as .hn
    · specialize #0 ≤ #0 with m @ efrom leRefl
      specialize #0 + 0 = #0 with m @ efrom addZero
      rw[←.hn, this]
    · have m < m + n
      · specialize 0 + #0 = #0 with m @ efrom zeroAdd
        ?
        then ∀ ∀ ∀ (#0 < #1 → #0 + #2 < #1 + #2) as .add_lt_add · from addLtAddPR
        specialize this with 0, n, m

  qed.

def numeralLtSucc {n m : ℕ} (h : n < m) : [] ⟹[T] “∀ ∀ #0 < #0 + 1 + #1” :=
  proof.
    generalize n; generalize m
    
    ?
  qed.
-/

def numeralAdd (n m : ℕ) : [] ⟹[T] “ᵀ!(SubTerm.natLit L n) + ᵀ!(SubTerm.natLit L m) = ᵀ!(SubTerm.natLit L (n + m))” := by
  induction' m with m ih
  · simp
    exact proofBy {
      then ∀ #0 + 0 = #0 · from addZeroPR
      specialize this with ᵀ!(SubTerm.Operator.const $ SubTerm.natLit L n) }
  · by_cases hm : m = 0
    · simp[hm, Nat.add_succ] at ih ⊢
      suffices : [] ⟹[T] “ᵀ!(SubTerm.natLit L n) + 1 = ᵀ!(SubTerm.natLit L (n + 1))”
      { exact this.cast (by rfl) }
      by_cases hn : n = 0
      · simp[hn]
        exact proofBy {
          then ∀ 0 + #0 = #0 · from zeroAdd
          specialize this with 1 }
      · simp[hn, SubTerm.natLit_succ]; exact proofBy { refl }
    · simp[hm, Nat.add_succ, SubTerm.natLit_succ]
      exact proof.
        then ᵀ!(SubTerm.natLit L n) + ᵀ!(SubTerm.natLit L m) = ᵀ!(SubTerm.natLit L (n + m)) as .ih · from ih
        then ∀ ∀ ∀ (#0 + #1) + #2 = #0 + (#1 + #2) as .add_assoc · from addAssocPR
        specialize this with ᵀ!(SubTerm.Operator.const $ SubTerm.natLit L n), ᵀ!(SubTerm.Operator.const $ SubTerm.natLit L m), 1
        rw[←this, .ih]
        refl
      qed.
      
def numeralMul (n m : ℕ) : [] ⟹[T] “ᵀ!(SubTerm.natLit L n) * ᵀ!(SubTerm.natLit L m) = ᵀ!(SubTerm.natLit L (n * m))” := by
  induction' m with m ih
  · simp
    exact proofBy {
      then ∀ #0 * 0 = 0 · from mulZeroPR
      specialize this with ᵀ!(SubTerm.Operator.const $ SubTerm.natLit L n) }
  · by_cases hm : m = 0
    · simp[hm, Nat.add_succ] at ih ⊢
      suffices : [] ⟹[T] “ᵀ!(SubTerm.natLit L n) * 1 = ᵀ!(SubTerm.natLit L n)”
      { exact this.cast (by rfl) }
      exact proofBy {
        then ∀ #0 * 1 = #0 · from mulOnePR
        specialize this with ᵀ!(SubTerm.Operator.const $ SubTerm.natLit L n) }
    · simp[hm, Nat.mul_succ, SubTerm.natLit_succ]
      exact proofBy {
        then ᵀ!(SubTerm.natLit L (n * m)) + ᵀ!(SubTerm.natLit L n) = ᵀ!(SubTerm.natLit L (n * m + n)) · from numeralAdd _ _
        then ᵀ!(SubTerm.natLit L n) * ᵀ!(SubTerm.natLit L m) = ᵀ!(SubTerm.natLit L (n * m)) as .ih · from ih
        then ∀ #0 * 1 = #0 · from mulOnePR
        specialize this with ᵀ!(SubTerm.Operator.const $ SubTerm.natLit L n) as .h
        then ∀ ∀ ∀ #0 * (#1 + #2) = #0 * #1 + #0 * #2 · from distrPR
        specialize this with ᵀ!(SubTerm.Operator.const $ SubTerm.natLit L n), ᵀ!(SubTerm.Operator.const $ SubTerm.natLit L m), 1
        rw[this, .h, .ih] }

def numeralLt {n m : ℕ} (h : n < m) : [] ⟹[T] “ᵀ!(SubTerm.natLit L n) < ᵀ!(SubTerm.natLit L m)” := sorry
  
def numeralNEq {n m : ℕ} (h : n ≠ m) : [] ⟹[T] “ᵀ!(SubTerm.natLit L n) ≠ ᵀ!(SubTerm.natLit L m)” := sorry

end PAminus

end Arith
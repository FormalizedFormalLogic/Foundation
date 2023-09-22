import Logic.Predicate.FirstOrder.Arith.Theory
import Logic.Predicate.FirstOrder.Principia.Meta

namespace LO

namespace FirstOrder
variable {L : Language.{u}} [L.ORing] [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]
variable {T : Theory L} [Arith.Robinson T]

namespace Arith

namespace Robinson

def succNeZero : [] ⟹[T] “∀ #0 + 1 ≠ 0” :=
  Principia.axmOfEq “∀ #0 + 1 ≠ 0” (by simp) (Arith.Robinson.robinson $ Theory.Robinson.q₁)

def succInj : [] ⟹[T] “∀ ∀ (#0 + 1 = #1 + 1 → #0 = #1)” :=
  Principia.axmOfEq “∀ ∀ (#0 + 1 = #1 + 1 → #0 = #1)” (by simp) (Arith.Robinson.robinson $ Theory.Robinson.q₂)

def zeroOrSucc : [] ⟹[T] “∀ (#0 = 0 ∨ (∃ #1 = #0 + 1))” :=
  Principia.axmOfEq “∀ (#0 = 0 ∨ (∃ #1 = #0 + 1))” (by simp) (Arith.Robinson.robinson $ Theory.Robinson.q₃)

def addZero : [] ⟹[T] “∀ #0 + 0 = #0” :=
  Principia.axmOfEq “∀ #0 + 0 = #0” (by simp) (Arith.Robinson.robinson $ Theory.Robinson.q₄)

def addSucc : [] ⟹[T] “∀ ∀ (#0 + (#1 + 1) = (#0 + #1) + 1)” :=
  Principia.axmOfEq “∀ ∀ (#0 + (#1 + 1) = (#0 + #1) + 1)” (by simp) (Arith.Robinson.robinson $ Theory.Robinson.q₅)

def mulZero : [] ⟹[T] “∀ #0 * 0 = 0” :=
  Principia.axmOfEq “∀ #0 * 0 = 0” (by simp) (Arith.Robinson.robinson $ Theory.Robinson.q₆)

def mulSucc : [] ⟹[T] “∀ ∀ #0 * (#1 + 1) = (#0 * #1) + #0” :=
  Principia.axmOfEq “∀ ∀ #0 * (#1 + 1) = (#0 * #1) + #0” (by simp) (Arith.Robinson.robinson $ Theory.Robinson.q₇)

def leIffEqOrLt : [] ⟹[T] “∀ ∀ (#0 ≤ #1 ↔ #0 = #1 ∨ #0 < #1)” :=
  by simp[SubFormula.le_eq]; exact proofBy { generalize x; generalize x; refl }

def leIffAdd : [] ⟹[T] “∀ ∀ (#0 ≤ #1 ↔ ∃ #0 + #1 = #2)” :=
  Principia.axmOfEq “∀ ∀ (#0 ≤ #1 ↔ ∃ #0 + #1 = #2)” (by simp) (Arith.Robinson.robinson $ Theory.Robinson.q₈)

def eqZeroOfAddEqZero : [] ⟹[T] “∀ ∀ (#0 + #1 = 0 → #0 = 0 ∧ #1 = 0)” :=
  proof.
    then ∀ #0 + 1 ≠ 0 as .ne_zero · from succNeZero
    then ∀ (#0 = 0 ∨ ∃ #1 = #0 + 1) as .zero_or_succ · from zeroOrSucc
    then ∀ #0 + 0 = #0 as .add_zero · from addZero
    then ∀ ∀ (#0 + (#1 + 1) = (#0 + #1) + 1) as .add_succ · from addSucc  
    generalize m; generalize n; intro as .h₀
    cases m = 0 as .h₁ or ∃ m = #0 + 1 as .h₁ @ specialize .zero_or_succ with m
    · cases n = 0 as .h₂ or ∃ n = #0 + 1 as .h₂
      @ specialize .zero_or_succ with n
      · split
      · choose n' st .h₂ as .h₃
        have n' + 1 = 0 as .contra
        · have n' + 1 + 0 = 0
          · rw[←.h₃, ←.h₁, .h₀]
          rewrite n' + 1 = n' + 1 + 0
          @ symmetry; specialize .add_zero with n' + 1
        have n' + 1 ≠ 0
        · specialize .ne_zero with n'
        contradiction .contra
    · choose m' st .h₁ as .h₂
      have (n + m') + 1 = 0 as .contra
      · rewrite (n + m') + 1 = n + (m' + 1)
        @ symmetry; specialize .add_succ with n, m'
        rewrite ←.h₂
      have (n + m') + 1 ≠ 0
      · specialize .ne_zero with n + m'
      contradiction .contra
  qed.

def eqSuccOfNeZero : [] ⟹[T] “∀ (#0 ≠ 0 → ∃ #1 = #0 + 1)” :=
  proof.
    then ∀ (#0 = 0 ∨ ∃ #1 = #0 + 1) as .zero_or_succ · from zeroOrSucc
    generalize n; intro
    cases n = 0 or ∃ n = #0 + 1
      @ specialize .zero_or_succ with n
      · have n ≠ 0 as .h · assumption
        contradiction .h
      · assumption
  qed.

def eqZeroOfMulEqZero : [] ⟹[T] “∀ ∀ (#0 * #1 = 0 → #0 = 0 ∨ #1 = 0)” :=
  proof.
    then ∀ #0 + 1 ≠ 0 as .succ_ne_zero · from succNeZero
    then ∀ (#0 ≠ 0 → ∃ #1 = #0 + 1) as .eq_succ_of_pos · from zeroOrSucc
    then ∀ ∀ (#0 + (#1 + 1) = (#0 + #1) + 1) as .add_succ · from addSucc 
    then ∀ ∀ (#0 * (#1 + 1) = (#0 * #1) + #0) as .mul_succ · from mulSucc
    generalize m; generalize n; intro as .h₀
    absurd as .ne_zero
    have ∃ n = #0 + 1
    · specialize .eq_succ_of_pos with n as .h
      apply .h
      · andl .ne_zero
    choose n' st this as .hn'
    have ∃ m = #0 + 1
    · specialize .eq_succ_of_pos with m as .h
      apply .h
      · andr .ne_zero
    choose m' st this as .hm'
    have n * m = (n' + 1)*m' + n' + 1 as .h₁
    · specialize .mul_succ with n' + 1, m' as .hms
      specialize .add_succ with (n' + 1)*m', n' as .has
      rw[.hn', .hm', .hms, .has]
      refl
    have (n' + 1)*m' + n' + 1 = 0
    · rw[←.h₁]
    have (n' + 1)*m' + n' + 1 ≠ 0
    · specialize .succ_ne_zero with (n' + 1)*m' + n'
    contradiction this
  qed.

def zeroBot : [] ⟹[T] “∀ 0 ≤ #0” :=
  proof.
    then ∀ (#0 + 0 = #0) as .add_zero · from addZero
    then ∀ ∀ (#0 ≤ #1 ↔ ∃ #0 + #1 = #2) as .le_def · from leIffAdd
    generalize n
    rewrite 0 ≤ n ↔ ∃ #0 + 0 = n
    @ specialize .le_def with 0, n
    use n
    specialize .add_zero with n
  qed.

end Robinson

end Arith

end FirstOrder
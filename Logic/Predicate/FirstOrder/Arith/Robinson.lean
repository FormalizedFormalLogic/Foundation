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
  by simp[SubFormula.le_eq]; exact proofBy { generalize; generalize; refl }

def leIffAdd : [] ⟹[T] “∀ ∀ (#0 ≤ #1 ↔ ∃ #0 + #1 = #2)” :=
  Principia.axmOfEq “∀ ∀ (#0 ≤ #1 ↔ ∃ #0 + #1 = #2)” (by simp) (Arith.Robinson.robinson $ Theory.Robinson.q₈)

def eqZeroOfAddEqZero : [] ⟹[T] “∀ ∀ (#0 + #1 = 0 → #0 = 0 ∧ #1 = 0)” :=
  proof.
    then ∀ #0 + 1 ≠ 0 as "ne zero" · from succNeZero
    then ∀ (#0 = 0 ∨ ∃ #1 = #0 + 1) as "zero or succ" · from zeroOrSucc
    then ∀ #0 + 0 = #0 as "add zero" · from addZero
    then ∀ ∀ (#0 + (#1 + 1) = (#0 + #1) + 1) as "add succ" · from addSucc  
    generalize; generalize; intro as "h₀"
    cases &1 = 0 as "h₁" or ∃ &1 = #0 + 1 as "h₁" @ specialize "zero or succ" with &1
    · cases &0 = 0 as "h₂" or ∃ &0 = #0 + 1 as "h₂"
      @ specialize "zero or succ" with &0
      · split
      · choose "h₂" as "h₃"
        have &0 + 1 = 0 as "contra"
        · have &0 + 1 + 0 = 0 · rew ←"h₃", ←"h₁", "h₀"
          rewrite &0 + 1 = &0 + 1 + 0
          @ symmetry; specialize "add zero" with &0 + 1
        have &0 + 1 ≠ 0
        · specialize "ne zero" with &0
        contradiction "contra"
    · choose "h₁" as "h₂"
      have (&1 + &0) + 1 = 0 as "contra"
      · rewrite (&1 + &0) + 1 = &1 + (&0 + 1)
        @ symmetry; specialize "add succ" with &1, &0
        rewrite ←"h₂"
      have (&1 + &0) + 1 ≠ 0 
      · specialize "ne zero" with &1 + &0
      contradiction "contra"
  qed.

def eqSuccOfNeZero : [] ⟹[T] “∀ (#0 ≠ 0 → ∃ #1 = #0 + 1)” :=
  proof.
    then ∀ (#0 = 0 ∨ ∃ #1 = #0 + 1) as "zero or succ" · from zeroOrSucc
    generalize; intro
    cases &0 = 0 or ∃ &0 = #0 + 1
      @ specialize "zero or succ" with &0
      · have &0 ≠ 0 as "h" · assumption
        contradiction "h"
      · assumption
  qed.

def eqZeroOfMulEqZero : [] ⟹[T] “∀ ∀ (#0 * #1 = 0 → #0 = 0 ∨ #1 = 0)” :=
  proof.
    then ∀ #0 + 1 ≠ 0 as "succ ne zero" · from succNeZero
    then ∀ (#0 ≠ 0 → ∃ #1 = #0 + 1) as "eq succ of pos" · from zeroOrSucc
    then ∀ ∀ (#0 + (#1 + 1) = (#0 + #1) + 1) as "add succ" · from addSucc 
    then ∀ ∀ (#0 * (#1 + 1) = (#0 * #1) + #0) as "mul succ" · from mulSucc
    generalize; generalize; intro as "h₀"
    absurd as "ne zero"
    have ∃ &0 = #0 + 1
    · specialize "eq succ of pos" with &0 as "h"
      apply "h"
      · andl "ne zero"
    choose this as "e₁"
    have ∃ &2 = #0 + 1
    · specialize "eq succ of pos" with &2 as "h"
      apply "h"
      · andr "ne zero"
    choose this as "e₂"
    have &2 * &3 = (&1 + 1)*&0 + &1 + 1 as "h₁"
    · specialize "mul succ" with &1 + 1, &0 as "ms"
      specialize "add succ" with (&1 + 1)*&0, &1 as "as"
      rew "e₁", "e₂", "ms", "as"
      refl
    have (&1 + 1)*&0 + &1 + 1 = 0
    · rew ←"h₁"
    have (&1 + 1)*&0 + &1 + 1 ≠ 0
    · specialize "succ ne zero" with (&1 + 1)*&0 + &1
    contradiction this
  qed.

def zeroBot : [] ⟹[T] “∀ 0 ≤ #0” :=
  proof.
    then ∀ (#0 + 0 = #0) as "add zero" · from addZero
    then ∀ ∀ (#0 ≤ #1 ↔ ∃ #0 + #1 = #2) as "le def" · from leIffAdd
    generalize
    rewrite 0 ≤ &0 ↔ ∃ #0 + 0 = &0
    @ specialize "le def" with 0, &0
    use &0
    specialize "add zero" with &0
  qed.

end Robinson

end Arith

end FirstOrder
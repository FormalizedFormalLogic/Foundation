import Logic.Predicate.FirstOrder.Arith.Theory
import Logic.Predicate.FirstOrder.Principia.Meta

namespace FirstOrder
variable {L : Language.{u}} [L.ORing] [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]
variable {T : Theory L} [T.RobinsonTheory]

namespace Arith

namespace Robinson

def succNeZero : [] ⟹[T] “∀ #0 + 1 ≠ 0” :=
  Principia.axmOfEq “∀ #0 + 1 ≠ 0” (by simp) (Theory.RobinsonTheory.robinson $ Theory.Arith.Robinson.q₁)

def succInj : [] ⟹[T] “∀ ∀ (#0 + 1 = #1 + 1 → #0 = #1)” :=
  Principia.axmOfEq “∀ ∀ (#0 + 1 = #1 + 1 → #0 = #1)” (by simp) (Theory.RobinsonTheory.robinson $ Theory.Arith.Robinson.q₂)

def zeroOrSucc : [] ⟹[T] “∀ (#0 = 0 ∨ (∃ #1 = #0 + 1))” :=
  Principia.axmOfEq “∀ (#0 = 0 ∨ (∃ #1 = #0 + 1))” (by simp) (Theory.RobinsonTheory.robinson $ Theory.Arith.Robinson.q₃)

def addZero : [] ⟹[T] “∀ #0 + 0 = #0” :=
  Principia.axmOfEq “∀ #0 + 0 = #0” (by simp) (Theory.RobinsonTheory.robinson $ Theory.Arith.Robinson.q₄)

def addSucc : [] ⟹[T] “∀ ∀ (#0 + (#1 + 1) = (#0 + #1) + 1)” :=
  Principia.axmOfEq “∀ ∀ (#0 + (#1 + 1) = (#0 + #1) + 1)” (by simp) (Theory.RobinsonTheory.robinson $ Theory.Arith.Robinson.q₅)

def mulZero : [] ⟹[T] “∀ #0 * 0 = 0” :=
  Principia.axmOfEq “∀ #0 * 0 = 0” (by simp) (Theory.RobinsonTheory.robinson $ Theory.Arith.Robinson.q₆)

def mulSucc : [] ⟹[T] “∀ ∀ #0 * (#1 + 1) = (#0 * #1) + #0” :=
  Principia.axmOfEq “∀ ∀ #0 * (#1 + 1) = (#0 * #1) + #0” (by simp) (Theory.RobinsonTheory.robinson $ Theory.Arith.Robinson.q₇)

def ltIff : [] ⟹[T] “∀ ∀ (#0 < #1 ↔ (∃ #0 + #1 + 1 = #2))” :=
  Principia.axmOfEq “∀ ∀ (#0 < #1 ↔ (∃ #0 + #1 + 1 = #2))” (by simp) (Theory.RobinsonTheory.robinson $ Theory.Arith.Robinson.q₈)

def eqZeroOfAddEqZero : [] ⟹[T] “∀ ∀ (#0 + #1 = 0 → #0 = 0 ∧ #1 = 0)” :=
  proof.
    then ∀ #0 + 1 ≠ 0 as "ne zero" · from succNeZero
    then ∀ (#0 = 0 ∨ ∃ #1 = #0 + 1) as "zero or succ" · from zeroOrSucc
    then ∀ #0 + 0 = #0 as "add zero" · from addZero
    then ∀ ∀ (#0 + (#1 + 1) = (#0 + #1) + 1) as "add succ" · from addSucc  
    generalize; generalize; intro
    cases &1 = 0 as "h₁" or ∃ &1 = #0 + 1 as "h₁" @ specialize &1 of "zero or succ"
    · cases &0 = 0 as "h₂" or ∃ &0 = #0 + 1 as "h₂"
      @ specialize &0 of "zero or succ"
      · split
      · choose "h₂" as "h₃"
        have &0 + 1 = 0 as "contra"
        · have &0 + 1 + 0 = 0
          · rewrite &0 + 1 ↦ &1
            rewrite 0 ↦ &2
            rewrite &1 + &2 ↦ 0
          rewrite &0 + 1 ↦ &0 + 1 + 0
          @ symmetry; specialize &0 + 1 of "add zero"
        have &0 + 1 ≠ 0
        · specialize &0 of "ne zero"
        contradiction "contra"
    · choose "h₁" as "h₂"
      have (&1 + &0) + 1 = 0 as "contra"
      · rewrite (&1 + &0) + 1 ↦ &1 + (&0 + 1)
        @ symmetry; specialize &1, &0 of "add succ"
        rewrite &0 + 1 ↦ &2
      have (&1 + &0) + 1 ≠ 0 
      · specialize &1 + &0 of "ne zero"
      contradiction "contra"
  qed.

def eqZeroOfMulEqZero : [] ⟹[T] “∀ ∀ (#0 * #1 = 0 → #0 = 0 ∧ #1 = 0)” :=
  by sorry

end Robinson

end Arith

end FirstOrder
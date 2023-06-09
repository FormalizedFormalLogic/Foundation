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

def eqZeroOfMulEqZero : [] ⟹[T] “∀ ∀ (#0 * #1 = 0 → #0 = 0 ∧ #1 = 0)” :=
  by sorry

end Robinson

end Arith

end FirstOrder
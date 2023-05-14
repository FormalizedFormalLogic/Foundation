import Logic.Predicate.FirstOrder.Arith.Theory
import Logic.Predicate.FirstOrder.Principia.Meta

namespace FirstOrder
variable {L : Language.{u}} [L.ORing] [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]
variable {T : Theory L} [T.RobinsonTheory]

namespace Arith

namespace Robinson

#check Principia.axm

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
    then ∀ #0 + 1 ≠ 0 · from succNeZero
    then ∀ (#0 = 0 ∨ ∃ #1 = #0 + 1) · from zeroOrSucc
    then ∀ #0 + 0 = #0 · from addZero
    then ∀ ∀ (#0 + (#1 + 1) = (#0 + #1) + 1) · from addSucc  
    generalize; generalize
    intro
    cases &1 = 0 or ∃ &1 = #0 + 1 @ specialize &1 of #0 = 0 ∨ ∃ #1 = #0 + 1
    · cases &0 = 0 or ∃ &0 = #0 + 1
      @ specialize &0 of #0 = 0 ∨ ∃ #1 = #0 + 1
      · split
      · choose &0 = #0 + 1
        have &0 + 1 = 0
        · have &0 + 1 + 0 = 0
          · rewrite &0 + 1 ↦ &1 @ symmetry
            rewrite 0 ↦ &2 @ symmetry
            rewrite &1 + &2 ↦ 0
            symmetry
          rewrite &0 + 1 ↦ &0 + 1 + 0
          @ symmetry; specialize &0 + 1 of #0 + 0 = #0
        have &0 + 1 ≠ 0
        · specialize &0 of #0 + 1 ≠ 0
        contradiction &0 + 1 = 0
    · choose &1 = #0 + 1
      have (&1 + &0) + 1 = 0
      · rewrite (&1 + &0) + 1 ↦ &1 + (&0 + 1)
        @ symmetry; specialize &1, &0 of #0 + (#1 + 1) = (#0 + #1) + 1
        rewrite &0 + 1 ↦ &2
        @ symmetry
      have (&1 + &0) + 1 ≠ 0 
      · specialize &1 + &0 of #0 + 1 ≠ 0
      contradiction (&1 + &0) + 1 = 0
  □

def eqZeroOfMulEqZero : [] ⟹[T] “∀ ∀ (#0 * #1 = 0 → #0 = 0 ∧ #1 = 0)” :=
  by sorry

end Robinson

end Arith

end FirstOrder
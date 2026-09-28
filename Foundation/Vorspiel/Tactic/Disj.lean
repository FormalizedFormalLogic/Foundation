module

public import Mathlib.Init

/-!
# The `disj` tactic

`disj n` selects the `n`-th disjunct of a goal that is an iterated disjunction, replacing the
chain of `left` and `right` (or of `Or.inl` and `Or.inr`) that would otherwise name it.
-/

public meta section

namespace Mathlib.Tactic

open Lean Meta Elab Tactic

private partial def numDisjuncts (e : Expr) : MetaM Nat := do
  let e ← whnfR e
  if e.isAppOfArity ``Or 2 then
    return (← numDisjuncts e.appArg!) + 1
  else
    return 1

private def applyOrSide (goal : MVarId) (side : Name) : MetaM MVarId := do
  match ← goal.applyConst side with
  | [goal] => return goal
  | goals => throwError "`{side}` left {goals.length} goals"

def selectDisjunct (goal : MVarId) (i : Nat) : MetaM MVarId := goal.withContext do
  let target ← goal.getType'
  let n ← numDisjuncts target
  if i = 0 then
    throwError "disjuncts are numbered from 1; `disj 1` selects the leftmost one"
  if n < i then
    throwError "the goal has {n} disjunct(s), but `disj {i}` was asked for{indentExpr target}"
  let mut goal := goal
  for _ in [0:i - 1] do
    goal ← applyOrSide goal ``Or.inr
  if i < n then
    goal ← applyOrSide goal ``Or.inl
  return goal

/--
`disj n` replaces a goal `p₁ ∨ p₂ ∨ ⋯ ∨ pₙ ∨ ⋯` by its `n`-th disjunct, counting from `1`; it
is `right` applied `n - 1` times followed by `left`. The disjuncts are those of the right-nested
chain the goal displays, so `disj 2` on `p ∨ (q ∨ r) ∨ s` leaves `q ∨ r`.
-/
elab (name := disj) "disj " i:num : tactic =>
  liftMetaTactic1 fun goal => selectDisjunct goal i.getNat

end Mathlib.Tactic

end

section

variable {p q r s : Prop}

example (hp : p) : p ∨ q ∨ r ∨ s := by disj 1; exact hp

example (hq : q) : p ∨ q ∨ r ∨ s := by disj 2; exact hq

example (hr : r) : p ∨ q ∨ r ∨ s := by disj 3; exact hr

example (hs : s) : p ∨ q ∨ r ∨ s := by disj 4; exact hs

example (hp : p) : p ∨ q := by disj 1; exact hp

example (hp : p) : p ∨ q := by
  fail_if_success disj 0;
  fail_if_success disj 3;
  disj 1;
  exact hp;

example (hq : q) : p ∨ (q ∨ r) ∨ s := by disj 2; disj 1; exact hq

end

module

public import Mathlib.Tactic.NormNum

@[expose]
public meta section

namespace Qq

open Mathlib Qq Lean Elab Meta Tactic

def rflQ {u : Level} {α : Q(Sort u)} (a : Q($α)) : Q($a = $a) := q(rfl)

def toQList {u : Level} {α : Q(Type u)} : List Q($α) → Q(List $α)
  |     [] => q([])
  | a :: v => q($a :: $(toQList v))

def memQList? {u : Level} {α : Q(Type u)} (a : Q($α)) :
    (l : List Q($α)) → MetaM <| Option Q($a ∈ $(toQList l))
  |     [] => return none
  | b :: l => do
    if (← isDefEq (← whnf a) (← whnf b)) then
      let e : Q($a = $b) := rflQ a
      return some q(List.mem_cons.mpr (Or.inl $e))
    else
      let some h ← memQList? a l | return none
      return some q(List.mem_cons_of_mem $b $h)

def memQList?' (a : Expr) (l : List Expr) : MetaM (Option Expr) := do
  let ⟨u, _, a⟩ ← inferTypeQ' a
  memQList? (u := u) a l

partial def ofQList {u : Level} {α : Q(Type u)} (l : Q(List $α)) : MetaM <| List Q($α) := do
  match l with
  |       ~q([]) => return []
  | ~q($a :: $l) => return a :: (← ofQList l)

end Qq

end

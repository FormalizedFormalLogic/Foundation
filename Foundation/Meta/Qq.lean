import Lean.Elab.Tactic.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Util.AtomM
import Foundation.Vorspiel.Vorspiel

namespace Qq

open Mathlib Qq Lean Elab Meta Tactic

def rflQ {α : Q(Sort u)} (a : Q($α)) : Q($a = $a) := q(rfl)

def toQList {α : Q(Type u)} : List Q($α) → Q(List $α)
  |     [] => q([])
  | a :: v => q($a :: $(toQList v))

lemma List.mem_of_eq {a b : α} {l} (h : a = b) : a ∈ b :: l := by simp [h]

lemma List.mem_of_mem {a b : α} {l : List α} (h : a ∈ l) : a ∈ b :: l := by simp [h]

lemma List.mem_singleton_of_eq (a b : α) (h : a = b) : a ∈ [b] := by simp [h]

def memQList? {α : Q(Type u)} (a : Q($α)) : (l : List Q($α)) → MetaM <| Option Q($a ∈ $(toQList l))
  |     [] => return none
  | b :: l => do
    if (← isDefEq (← whnf a) (← whnf b)) then
      let e : Q($a = $b) := rflQ a
      return some q(List.mem_of_eq $e)
    else
      let some h ← memQList? a l | return none
      return some q(List.mem_of_mem $h)

def memQList?' (a : Expr) (l : List Expr) : MetaM (Option Expr) := do
  let ⟨u, _, a⟩ ← inferTypeQ' a
  memQList? (u := u) a l

partial def ofQList {α : Q(Type u)} (l : Q(List $α)) : MetaM <| List Q($α) := do
  match l with
  |       ~q([]) => return []
  | ~q($a :: $l) => return a :: (← ofQList l)

end Qq

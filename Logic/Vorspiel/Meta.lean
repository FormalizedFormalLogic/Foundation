import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Clear!
import Mathlib.Util.AtomM
import Logic.Vorspiel.Vorspiel
import Mathlib.Data.Fin.Fin2

open Qq Lean Elab Meta Tactic

universe u v

namespace Qq

def rflQ {α : Q(Sort u)} (a : Q($α)) : Q($a = $a) := q(rfl)

set_option linter.unusedVariables false in
def decideTQ (p : Q(Prop)) : MetaM Q($p) := do
  let dec : Q(Decidable $p) ← synthInstanceQ q(Decidable $p)
  let h : Q(decide $p = true) := rflQ q(true)
  return q(of_decide_eq_true $h)

def finQVal {n : Q(ℕ)} (e : Q(Fin $n)) : MetaM (Option ℕ) := do
  let val : Q(ℕ) ← whnf q(Fin.val $e)
  val.natLit?

-- Returns literal f e when e is literal
def natAppFunQ (f : ℕ → ℕ) (e : Q(ℕ)) : MetaM Q(ℕ) := do
  let e : Q(ℕ) ← whnf e
  let some n := Lean.Expr.natLit? e | throwError "not ℕ"
  Lean.Expr.ofNat q(ℕ) (f n)

-- https://leanprover-community.github.io/mathlib4_docs//Mathlib/Tactic/Linarith/Verification.html#Qq.inferTypeQ'
def inferSortQ' (e : Expr) : MetaM ((u : Level) × (α : Q(Sort $u)) × Q($α)) := do
  let α ← inferType e
  let .sort u ← instantiateMVars (← whnf (← inferType α))
    | throwError "not a type{indentExpr α}"
  pure ⟨u, α, e⟩

-- given an Expr e representing type α : Sort u, returns u and q(α)
def checkSortQ' (e : Expr) : MetaM (Option ((u : Level) × Q(Sort $u))) := do
  if let ⟨.succ u, α, e⟩ ← inferSortQ' e then
    if ← isDefEq α q(Sort $u) then
      return some ⟨u, e⟩
    else return none
  else return none

def inferSortQOfUniverse' (e : Expr) (ty : Q(Sort $u)) : MetaM (Option Q($ty)) := do
  if let ⟨.succ _, α, e⟩ ← inferSortQ' e then
    if ← isDefEq α q($ty) then
      return some e
    else return none
  else return none

set_option linter.unusedVariables false in
def MditeQ {α : Q(Sort u)} (c : Q(Prop)) (dec : Q(Decidable $c)) (t : MetaM Q($c → $α)) (e : MetaM Q(¬$c → $α)) : MetaM Q($α) := do
  let t ← t
  let e ← e
  return q(dite $c (fun h => $t h) (fun h => $e h))

set_option linter.unusedVariables false in
def BEqQ {α : Q(Sort u)} {a b : Q($α)} (h : a == b) : Q($a = $b) := (q(@rfl $α $a) : Expr)

def eqQUnsafe {α : Q(Sort u)} (a b : Q($α)) : Q($a = $b) := (q(@rfl $α $a) : Expr)

def toQList {α : Q(Type u)} : List Q($α) → Q(List $α)
  | []     => q([])
  | a :: v => q($a :: $(toQList v))

partial def ofQList {α : Q(Type u)} (l : Q(List $α)) : MetaM $ List Q($α) := do
  match l with
  | ~q([])       => return []
  | ~q($a :: $l) => return a :: (← ofQList l)

def isStrongEq (t s : Expr) : MetaM Bool := do isDefEq (← whnf t) (← whnf s)

elab "test₁" : term => do
  let e₁ : Q(Fin 3) := q(2)
  let e₂ : Q(Fin (.succ (.succ 1))) := q(Fin.succ 1)
  let b₁ := e₁ == e₂
  let b₂ ← isDefEq e₁ e₂
  let b₃ ← isStrongEq e₁ e₂
  logInfo m!"e₁ == e₂: {b₁}"
  logInfo m!"isDefEq e₁ e₂: {b₂}"
  logInfo m!"isStrongEq e₁ e₂: {b₃}"
  return q(0)

#eval test₁

section List
variable {α : Type u}

lemma List.mem_of_eq {a b : α} {l} (h : a = b) : a ∈ b :: l := by simp[h]

lemma List.mem_of_mem {a b : α} {l : List α} (h : a ∈ l) : a ∈ b :: l := by simp[h]

def memQList? {α : Q(Type u)} (a : Q($α)) : (l : List Q($α)) → MetaM $  Option Q($a ∈ $(toQList (u := u) l))
  | []     => return none
  | b :: l => do
      if (← isDefEq (← whnf a) (← whnf b)) then
        let e : Q($a = $b) := rflQ a
        return some q(List.mem_of_eq $e)
      else
        let some h ← memQList? a l | return none
        return by simp at h ⊢; exact some q(List.mem_of_mem $h)

example : 2 ∈ [3,4,5,2,6] := of_decide_eq_true rfl

lemma List.cons_congr {a b : α} {l k : List α} (ha : a = b) (hl : l = k) : a :: l = b :: k :=
  congr_arg₂ _ ha hl

def resultList {α : Q(Type u)} (res : (a : Q($α)) → MetaM ((res : Q($α)) × Q($a = $res))) :
    (l : List Q($α)) → MetaM ((lres : List Q($α)) × Q($(toQList (u := u) l) = $(toQList (u := u) lres)))
  | []     => pure ⟨[], q(rfl)⟩
  | a :: l => do
    let ⟨an, e⟩ ← res a
    let ⟨ihl, ihe⟩ ← resultList res l
    return ⟨an :: ihl, q(List.cons_congr $e $ihe)⟩

def funResultList {α β : Q(Type u)} (f : Q($α → $β)) (res : (a : Q($α)) → MetaM ((res : Q($β)) × Q($f $a = $res))) :
    (l : List Q($α)) → MetaM ((lres : List Q($β)) × Q(List.map $f $(toQList (u := u) l) = $(toQList (u := u) lres)))
  | []     => pure ⟨[], q(rfl)⟩
  | a :: l => do
    let ⟨an, e⟩ ← res a
    let ⟨ihl, ihe⟩ ← funResultList f res l
    return ⟨an :: ihl, q(List.cons_congr $e $ihe)⟩

end List

structure Result (α : Q(Type u)) where
  intro : (e : Q($α)) → MetaM $ (res : Q($α)) × Q($e = $res)

structure FunResult {α : Q(Type u)} {β : Q(Type v)} (f : Q($α → $β)) where
  intro : (e : Q($α)) → MetaM $ (res : Q($β)) × Q($f $e = $res)

namespace Result
variable {α : Q(Type u)}

def refl : Result α := ⟨fun e => pure ⟨e, q(rfl)⟩⟩

end Result

namespace ResultFun
variable {α : Q(Type u)} {β : Q(Type v)} (f : Q($α → $β))

def refl (e : Q($α)) : FunResult f := ⟨fun e => pure ⟨q($f $e), q(rfl)⟩⟩

end ResultFun

end Qq

namespace List
variable {m : Type → Type v} [inst : Monad m] {α : Type u}

def elemM (r : α → α → m Bool) (a : α) : List α → m Bool
  | [] => return false
  | b :: bs => do
    if (← r a b) then
      return true
    else
      bs.elemM r a

end List
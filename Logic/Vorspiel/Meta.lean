import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Clear!
import Mathlib.Util.AtomM
import Logic.Vorspiel.Vorspiel
import Mathlib.Data.Fin.Fin2

open Qq Lean Elab Meta Tactic

universe u v

inductive DbgResult (α : Type u) : α → Type u
  | intro : (a b : α) → a = b → DbgResult α a

instance {α} (a : α) : ToString (DbgResult α a) := ⟨fun r =>
  match r with
  | DbgResult.intro _ _ _ => "🎉 Proof Success! 🎉"⟩

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

elab "equalTest" : term => do
  let e₁ : Q(Fin 3) := q(2)
  let e₂ : Q(Fin (.succ (.succ 1))) := q(Fin.succ 1)
  let b₁ := e₁ == e₂
  let b₂ ← isDefEq e₁ e₂
  let b₃ ← isStrongEq e₁ e₂
  logInfo m!"e₁ == e₂: {b₁}"
  logInfo m!"isDefEq e₁ e₂: {b₂}"
  logInfo m!"isStrongEq e₁ e₂: {b₃}"
  return q(0)

#eval equalTest

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

structure Result {α : Q(Type u)} (e : Q($α)) where
  res : Q($α)
  eq : Q($e = $res)

structure ResultFun {α : Q(Type u)} {β : Q(Type v)} (f : Q($α → $β)) (e : Q($α)) where
  res : Q($β)
  eq : Q($f $e = $res)

namespace Result
variable {α : Q(Type u)}

def refl (e : Q($α)) : Result e := ⟨e, q(rfl)⟩

end Result

namespace ResultFun
variable {α : Q(Type u)} {β : Q(Type v)} (f : Q($α → $β))

def refl (e : Q($α)) : ResultFun f e := ⟨q($f $e), q(rfl)⟩

end ResultFun

lemma compVecEmpty {α : Type u} {β : Type v} (f : α → β) : f ∘ ![] = ![] := by simp

lemma compVecCons {α : Type u} {β : Type v} (f : α → β) {n}
  {a : α} {as : Fin n → α} {b : β} {bs : Fin n → β} (hb : f a = b) (hbs : f ∘ as = bs) :
    f ∘ (a :> as) = b :> bs := by simp[Function.comp, Matrix.comp_vecCons, hb, ←hbs]

lemma vecConsExt {α : Type u} {n}
  {a : α} {as : Fin n → α} {b : α} {bs : Fin n → α} (hb : a = b) (hbs : as = bs) :
    a :> as = b :> bs := hb ▸ hbs ▸ rfl

partial def resultVectorOfResult {α : Q(Type u)}
  (r : (e : Q($α)) → MetaM ((r : Q($α)) × Q($e = $r)))
  (n : Q(ℕ)) (l : Q(Fin $n → $α)) : MetaM ((l' : Q(Fin $n → $α)) × Q($l = $l')) := do
  match n with
  | ~q(0) =>
    match l with
    | ~q(![]) =>
      return ⟨q(![]), q(rfl)⟩
  | ~q($n + 1) =>
    let l : Q(Fin ($n + 1) → $α) := l
    match l with
    | ~q($a :> $as) =>
      let ⟨b, be⟩ ← r a
      let ⟨bs, bse⟩ ← resultVectorOfResult r n as
      return ⟨q($b :> $bs), q(vecConsExt $be $bse)⟩
    | _ => throwError m!"error in resultVectorOfResult(2). nonexhaustive match: {l}"
  | _ => throwError m!"error in resultVectorOfResult(1). nonexhaustive match: {n}"

partial def resultVectorOfResultFun {α : Q(Type u)} {β : Q(Type v)}
  (f : Q($α → $β)) (r : (e : Q($α)) → MetaM ((r : Q($β)) × Q($f $e = $r)))
  (n : Q(ℕ)) (l : Q(Fin $n → $α)) : MetaM ((l' : Q(Fin $n → $β)) × Q($f ∘ $l = $l')) := do
  match n with
  | ~q(0) =>
    match l with
    | ~q(![]) =>
      return ⟨q(![]), q(compVecEmpty $f)⟩
  | ~q($n + 1) =>
    let l : Q(Fin ($n + 1) → $α) := l
    match l with
    | ~q($a :> $as) =>
      let ⟨b, be⟩ ← r a
      let ⟨bs, bse⟩ ← resultVectorOfResultFun f r n as
      return ⟨q($b :> $bs), q(compVecCons $f $be $bse)⟩
    | _ => throwError m!"error in resultVectorOfResultFun(2). nonexhaustive match: {n}, {l}"
  | _ => throwError m!"error in resultVectorOfResultFun(1). nonexhaustive match: {n}"

partial def mapVectorInfo {α : Q(Type u)} {β : Q(Type v)} {H : Q($α → $β → Sort w)}
  (r : (a : Q($α)) → MetaM ((b : Q($β)) × Q($H $a $b)))
  (n : Q(ℕ)) (l : Q(Fin $n → $α)) : MetaM ((b : Q(Fin $n → $β)) × Q((i : Fin $n) → $H ($l i) ($b i))) := do
  match n with
  | ~q(0)      =>
    match l with
    | ~q(![])  =>
      return ⟨q(![]), q(finZeroElim)⟩
  | ~q($n + 1) =>
    let l : Q(Fin ($n + 1) → $α) := l
    match l with
    | ~q($a :> $as) =>
      let p ← r a
      let ps ← mapVectorInfo r n as
      let vectorConsQ
        {as : Q(Fin $n → $α)}
        {bs : Q(Fin $n → $β)}
        (ih : Q((i : Fin $n) → $H ($as i) ($bs i)))
        {a : Q($α)} {b : Q($β)} (h : Q($H $a $b)) : Q((i : Fin ($n + 1)) → $H (($a :> $as) i) (($b :> $bs) i)) :=
        q(Fin.cases $h $ih)
      have h : Q((i : Fin ($n + 1)) → $H (($a :> $as) i) (($(p.1) :> $(ps.1)) i)) := vectorConsQ ps.2 p.2
      return ⟨q($(p.1) :> $(ps.1)), h⟩
    | _ => throwError m!"error in mapVectorInfo(2). nonexhaustive match: {n}, {l}"
  | _ => throwError m!"error in mapVectorInfo(1). nonexhaustive match: {n}"

-- def Result.toVector (n : Q(ℕ)) {α: Q(Type u)}
--   (r : (e : Q($α)) → MetaM (Result e)) : (v : Q(Fin $n → $α)) → MetaM (Result (u := u) v) :=
--   resultVectorOfResult (fun e => do by {  })

partial def mapVectorQ {α : Q(Type u)} {β : Q(Type v)} (f : Q($α) → MetaM Q($β))
    (n : Q(ℕ)) (l : Q(Fin $n → $α)) : MetaM Q(Fin $n → $β) := do
  match n with
  | ~q(0) =>
    match l with
    | ~q(![]) =>
      return q(![])
  | ~q($n + 1) =>
    let l : Q(Fin ($n + 1) → $α) := l
    match l with
    | ~q($a :> $as) =>
      let b : Q($β) ← f a
      let bs : Q(Fin $n → $β) ← mapVectorQ f n as
      return q($b :> $bs)
    | _ => throwError m!"error in mapVectorQ(2). nonexhaustive match: {l}"
  | _ => throwError m!"error in mapVectorQ(1). nonexhaustive match: {n}"

elab "dbgmapVectorQ" : term => do
  let f : Q(ℕ) → MetaM Q(ℕ) := fun x => whnf q($x * 3)
  let v : Q(Fin 5 → ℕ) := q(![0,1,2,3,4])
  let e ← mapVectorQ (u := levelZero) (α := q(ℕ)) (β := q(ℕ)) f q(5) v
  logInfo m! "{e}"
  return e

#eval dbgmapVectorQ

partial def vectorQNthAux {α : Q(Type u)}
    (n : Q(ℕ)) (l : Q(Fin $n → $α)) (i : ℕ) : MetaM Q($α) := do
  match n with
  | ~q(0) => throwError m!"out of bound"
  | ~q($n + 1) =>
    let l : Q(Fin ($n + 1) → $α) := l
    match l with
    | ~q($a :> $l') =>
      match i with
      | 0        => return a
      | .succ i' => vectorQNthAux n l' i'
    | _ => throwError m!"error in vectorQNthAux(2). nonexhaustive match: {l}"
  | _ => throwError m!"error in vectorQNthAux(1). nonexhaustive match: {n}"
  

partial def vectorQNth {α : Q(Type u)}
    (n : Q(ℕ)) (l : Q(Fin $n → $α)) (i : Q(Fin $n)) : MetaM ((a : Q($α)) × Q($l $i = $a)) := do
    let some ival ← finQVal i | throwError m!"{i} should be numeral"
    let r ← vectorQNthAux (u := u) n l ival
    --let eq ← decideTQ q($l $i = $r)
    let eq : Expr := q(@rfl $α $r)
    return ⟨r, eq⟩

elab "dbgvectorQNth" : term => do
  let v : Q(Fin 5 → ℕ) := q(![0,1 + 8,2 + 8,3,4])
  let ⟨e, eq⟩ ← vectorQNth (α := q(ℕ)) q(5) v q(2)
  let dbgr := q(DbgResult.intro _ $e $eq)
  logInfo m! "{e}"
  logInfo m! "{eq}"
  return dbgr

#eval dbgvectorQNth

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

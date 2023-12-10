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

def inferPropQ' (e : Expr) : MetaM ((p : Q(Prop)) × Q($p)) := do
  let ⟨u, α, e⟩ ← inferSortQ' e
  if u == levelZero then
    return ⟨α, e⟩
  else throwError "not a prop {indentExpr α}"

-- TODO: fix
def inferPropQ (e : Expr) : MetaM Q(Prop) := do
  return e

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

section List
variable {α : Type u}

lemma List.mem_of_eq {a b : α} {l} (h : a = b) : a ∈ b :: l := by simp[h]

lemma List.mem_of_mem {a b : α} {l : List α} (h : a ∈ l) : a ∈ b :: l := by simp[h]

lemma List.cases_of_mem_cons {p : α → Prop} {a a' : α} {l : List α} (h : a' ∈ a :: l)
    (hl : ∀ a' ∈ l, p a') (ha : p a) : p a' := by
  rcases List.mem_cons.mp h with (h | h)
  · simpa[h]
  · exact hl _ h

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

def vecFold (α : Q(Type u)) :
    {n : ℕ} → (Fin n → Q($α)) → Q(Fin $n → $α)
  | 0,     _ => q(![])
  | _ + 1, v =>
    let ih := vecFold α (v ·.succ)
    q($(v 0) :> $ih)

def vecFoldDep : {n : ℕ} → (α : Q(Fin $n → Sort u)) → ((i : Fin n) → Q($α $i)) → Q((i : Fin $n) → $α i)
  | 0,     _, _ => q(finZeroElim)
  | _ + 1, _, v =>
    let ih := vecFoldDep _ (v ·.succ)
    q(Fin.cases $(v 0) $ih)

def vecUnfold (α : Q(Type u)) :
    (n : ℕ) → Q(Fin $n → $α) → MetaM (Fin n → Q($α))
  | 0,     _ => pure finZeroElim
  | n + 1, v =>
    match v with
    | ~q($a :> $w) => do
      let ih ←vecUnfold α n w
      return a :> ih

lemma eq_cons_app_succ_of_eq {α : Type u} {a b : α} {as : Fin n → α} {i : Fin n}
  (has : as i = b) : (a :> as) i.succ = b := by simp[has]

partial def vectorGet {α : Q(Type u)} :
    {n : ℕ} → (l : Q(Fin $n → $α)) → (i : Fin n) → MetaM ((a : Q($α)) × Q($l $i = $a))
  | 0,     _, i => Fin.elim0 i
  | n + 1, l, i =>
    match l with
    | ~q($a :> $as) =>
      i.cases (pure ⟨q($a), q(rfl)⟩)
        (fun i : Fin n => do
          let ⟨b, hb⟩ ← vectorGet as i
          return ⟨q($b), q(eq_cons_app_succ_of_eq $hb)⟩)

partial def mapVector {α : Q(Type u)} {β : Q(Type v)}
  (r : Q($α) → MetaM Q($β))
  (n : Q(ℕ)) (l : Q(Fin $n → $α)) : MetaM Q(Fin $n → $β) := do
  match n with
  | ~q(0) =>
    match l with
    | ~q(![]) =>
      return q(![])
  | ~q($n + 1) =>
    match l with
    | ~q($a :> $as) =>
      let b ← r a
      let bs ← mapVector r n as
      return q($b :> $bs)
    | _ => throwError m!"error in mapVector(2). nonexhaustive match: {n}, {l}"
  | _ => throwError m!"error in mapVector(1). nonexhaustive match: {n}"

partial def resultVectorOfResult {α : Q(Type u)}
  (r : (e : Q($α)) → MetaM ((r : Q($α)) × Q($e = $r)))
  (n : Q(ℕ)) (l : Q(Fin $n → $α)) : MetaM ((l' : Q(Fin $n → $α)) × Q($l = $l')) := do
  match n with
  | ~q(0) =>
    match l with
    | ~q(![]) =>
      return ⟨q(![]), q(rfl)⟩
  | ~q($n + 1) =>
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
    match l with
    | ~q($a :> $as) =>
      let ⟨b, be⟩ ← r a
      let ⟨bs, bse⟩ ← resultVectorOfResultFun f r n as
      return ⟨q($b :> $bs), q(compVecCons $f $be $bse)⟩
    | _ => throwError m!"error in resultVectorOfResultFun(2). nonexhaustive match: {n}, {l}"
  | _ => throwError m!"error in resultVectorOfResultFun(1). nonexhaustive match: {n}"

partial def vectorCollection {α : Q(Type u)} {β : Q(Type v)} {H : Q($α → $β → Sort w)}
  (r : (a : Q($α)) → MetaM ((b : Q($β)) × Q($H $a $b)))
  (n : Q(ℕ)) (l : Q(Fin $n → $α)) : MetaM ((b : Q(Fin $n → $β)) × Q((i : Fin $n) → $H ($l i) ($b i))) := do
  match n with
  | ~q(0)      =>
    match l with
    | ~q(![])  =>
      return ⟨q(![]), q(finZeroElim)⟩
  | ~q($n' + 1) =>
    match l with
    | ~q($a :> $as) =>
      let p ← r a
      let ps ← vectorCollection r n' as
      let vectorConsQ
        {as : Q(Fin $n' → $α)}
        {bs : Q(Fin $n' → $β)}
        (ih : Q((i : Fin $n') → $H ($as i) ($bs i)))
        {a : Q($α)} {b : Q($β)} (h : Q($H $a $b)) : Q((i : Fin ($n' + 1)) → $H (($a :> $as) i) (($b :> $bs) i)) :=
        q(Fin.cases $h $ih)
      have h : Q((i : Fin ($n' + 1)) → $H (($a :> $as) i) (($(p.1) :> $(ps.1)) i)) := vectorConsQ ps.2 p.2
      return ⟨q($(p.1) :> $(ps.1)), h⟩
    | _ => throwError m!"error in vectorCollection(2). nonexhaustive match: {n}, {l}"
  | _ => throwError m!"error in vectorCollection(1). nonexhaustive match: {n}"

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
  | ~q($n' + 1) =>
    match l with
    | ~q($a :> $as) =>
      let b : Q($β) ← f a
      let bs : Q(Fin $n' → $β) ← mapVectorQ f n' as
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
  match i with
  | 0 =>
    match n with
    | ~q(0) => throwError m!"out of bound"
    | ~q($n + 1) =>
      match l with
      | ~q($a :> _) => return a
      | _ => throwError m!"error in vectorQNthAux(2). nonexhaustive match: {l}"
  | .succ i' =>
    match n with
    | ~q(0) => throwError m!"out of bound"
    | ~q($n + 1) =>
      match l with
      | ~q(_ :> $l') => vectorQNthAux n l' i'
      | _ => throwError m!"error in vectorQNthAux(2). nonexhaustive match: {l}"

partial def vectorQNth {α : Q(Type u)}
    (n : Q(ℕ)) (l : Q(Fin $n → $α)) (i : Q(Fin $n)) : MetaM ((a : Q($α)) × Q($l $i = $a)) := do
    let some ival ← finQVal i | throwError m!"{i} should be numeral"
    let r ← vectorQNthAux (u := u) n l ival
    --let eq ← decideTQ q($l $i = $r)
    let eq : Expr := q(@rfl $α $r)
    return ⟨r, eq⟩

elab "dbgvectorQNth" : term => do
  let v : Q(Fin 5 → ℕ) := q(![0,1 + 8,2 + 8,3,4])
  let ⟨e, eq⟩ ← vectorQNth (α := q(ℕ)) q(5) v q(2+1)
  let dbgr := q(DbgResult.intro _ $e $eq)
  logInfo m! "{e}"
  logInfo m! "{eq}"
  return dbgr

private lemma vecCons_assoc_eq {a b : α} {s : Fin n → α} (h : s <: b = t) :
    (a :> s) <: b = a :> t := by simp[←h, Matrix.vecCons_assoc]

partial def vectorAppend {α : Q(Type u)}
    (n : Q(ℕ)) (v : Q(Fin $n → $α)) (a : Q($α)) : MetaM ((w : Q(Fin ($n + 1) → $α)) × Q($v <: $a = $w)) := do
  match n with
  | ~q(0) => return ⟨q(![$a]), q(Matrix.vecConsLast_vecEmpty $a)⟩
  | ~q($n' + 1) =>
    match v with
    | ~q($b :> $v') =>
      let ⟨ih, ihh⟩ ← vectorAppend n' v' a
      return ⟨q($b :> $ih), q(vecCons_assoc_eq $ihh)⟩
    | _ => throwError m!"error in vectorQNthAux(2). nonexhaustive match: {v}"

elab "dbgVectorAppend" : term => do
  let v : Q(Fin 5 → ℕ) := q(![0,1 + 8,2 + 8,3,4])
  let a : Q(ℕ) := q(8)
  let ⟨w, eq⟩ ← vectorAppend (u := levelZero) q(5) v a
  let dbgr := q(DbgResult.intro _ _ $eq)
  logInfo m! "{w}"
  logInfo m! "{eq}"
  return dbgr

end Qq

namespace Lean

namespace Expr

def stringLit? : Expr → Option String
  | lit (Literal.strVal s) => some s
  | _                      => none

end Expr

end Lean

namespace List
variable {m : Type → Type v} [inst : Monad m] {α : Type u}

def elemM (r : α → α → m Bool) (a : α) : List α → m Bool
  | []      => return false
  | b :: bs => do
    if (← r a b) then
      return true
    else
      bs.elemM r a

end List

class ExprNamed (α : Type) where
  name : Q(Type)

instance : ExprNamed ℕ := ⟨q(ℕ)⟩

instance : ExprNamed ℕ := ⟨q(ℕ)⟩

class Denotation (σ : outParam (Q(Type*))) (α : Type) where
  denote' : Q($σ) → MetaM α
  toExpr' : α → Q($σ)

namespace Denotation

abbrev denote (σ : Q(Type*)) {α} [Denotation σ α] : Q($σ) → MetaM α := denote'

abbrev toExpr (σ : Q(Type*)) {α} [Denotation σ α] : α → Q($σ) := toExpr'

instance nat : Denotation q(ℕ) ℕ where
  denote' := fun e => do
    let some n := Lean.Expr.natLit? (←whnf e) | throwError "error in denotationNat: {e}"
    return n
  toExpr' := fun n : ℕ => q($n)

instance {n : ℕ} : Denotation q(Fin $n) (Fin n) where
  denote' := fun e => do
    let some i' := ←@Qq.finQVal q($n) (←whnf e) | throwError m! "error in denotationFin₁: {e}"
    let some i := n.toFin i' | throwError m! "error in denotationFin₂: {i'}"
    return i
  toExpr' := fun i : Fin n => q($i)

instance : Denotation q(String) String where
  denote' := fun e => do
    let some s := Lean.Expr.stringLit? (←whnf e) | throwError m!"error in DenotationString : {e}"
    return s
  toExpr' := fun s : String => q($s)

instance list {σ : Q(Type*)} {α : Type} [Denotation σ α] : Denotation q(List $σ) (List α) where
  denote' := fun e => do (← ofQList e).mapM (denote σ)
  toExpr' := fun l => toQList (l.map toExpr')

abbrev denoteₗ {σ : Q(Type*)} {α} (d : Denotation σ α) : Q(List $σ) → MetaM (List α) := denote' (self := list)

abbrev toExprₗ {σ : Q(Type*)} {α} (d : Denotation σ α) : List α → Q(List $σ) := toExpr' (self := list)

def memList? {σ : Q(Type*)} (d : Denotation σ α) (a : α) (l : List α) :
  MetaM $ Option Q($(toExpr σ a) ∈ $(toExprₗ d l)) := memQList? (toExpr σ a) (l.map toExpr')

local elab "dbgDList" : term => do
  let xExpr : Q(List ℕ) := q([0,1 + 8,2 + 8,3,4])
  let x : List ℕ ← denote q(List ℕ) xExpr
  logInfo m! "x: {x}"

  let y : List ℕ := [99, 2, 3]
  let yExpr := toExpr q(List ℕ) y
  let y : List ℕ ← denote q(List ℕ) yExpr
  let some mem ← memList? nat 2 y | throwError "xxx"
  logInfo m! "y: {mem}"
  return yExpr

def listSigmaImpliment {σ : Q(Type*)} (d : Denotation σ α) {p : Q($σ → Prop)} :
    (l : List ((a : α) × Q($p $(toExpr σ a)))) → MetaM Q(∀ a' ∈ $(toExprₗ d (l.map Sigma.fst)), $p a')
  | []     => return q(fun a h => False.elim (List.not_mem_nil a h))
  | ⟨a, ha⟩ :: l => do
    let ih ← listSigmaImpliment d l
    return (by simp at ha ih ⊢; exact q(fun _ ha' => List.cases_of_mem_cons ha' $ih $ha))

variable {σ τ : Q(Type*)} {α β : Type}
  [Denotation σ α] [Denotation τ β]

protected def isDefEq (a₁ a₂ : α) : MetaM Bool :=
  Lean.Meta.isDefEq (toExpr σ a₁) (toExpr σ a₂)

variable (σ)

structure DEq (a₁ a₂ : α) where
  expr : Q($(toExpr σ a₁) = $(toExpr σ a₂))

local notation:25 a₁ " ≡[" σ:25 "] " a₂:0 => DEq σ a₁ a₂

variable {σ}

structure DEqFun (f : Q($σ → $τ)) (a : α) (b : β) where
  expr : Q($f $(toExpr σ a) = $(toExpr τ b))

local notation:25 f "⟨" p₁:25 "⟩ ≡ " p₂:0 => DEqFun f p₁ p₂

namespace DEq

@[refl] protected def refl (a : α) : a ≡[σ] a := .mk q(rfl)

@[symm] protected def symm {a₁ a₂ : α} (h : a₁ ≡[σ] a₂) : a₂ ≡[σ] a₁ :=
  .mk q(Eq.symm $h.expr)

@[trans] protected def trans {a₁ a₂ a₃ : α} (h₁ : a₁ ≡[σ] a₂) (h₂ : a₂ ≡[σ] a₃) : a₁ ≡[σ] a₃ :=
  .mk q(Eq.trans $h₁.expr $h₂.expr)

end DEq

end Denotation

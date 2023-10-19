import Logic.Predicate.FirstOrder.Basic
open Qq Lean Elab Meta Tactic Term

namespace LO

namespace FirstOrder

open Rew

namespace Subterm

namespace Meta

variable {L : Q(Language.{u})} 

def _root_.List.subtAt {α : Type u} (n s : ℕ) (a : α) : List (Option α) :=
  List.ofFn fun (i : Fin n) => if i = s then some a else none

def _root_.List.optCombine {α : Type u} (l₁ l₂ : List (Option α)) : List (Option α) :=
  List.zipWith (fun x y =>
    match x, y with
    | none,   none   => none
    | some a, _      => some a
    | none,   some a => some a) l₁ l₂

def ListToVec (α : Q(Type u)) : List Q($α) → (k : ℕ) → MetaM Q(Fin $k → $α)
  | _,      0     => pure q(![])
  | a :: l, k + 1 => do
    let ih ← ListToVec α l k
    return q($a :> $ih)
  | [],     _ + 1 => throwError "error in ListToVec"

partial def dropFvar (L : Q(Language.{u})) (n : ℕ) : Q(SyntacticSubterm $L ($n + 1)) → MetaM Q(SyntacticSubterm $L $n)
  | ~q(&$x)                          => pure q(&$x)
  | ~q(func (arity := $arity) $f $v) => do
    let v' ← Qq.mapVector (α := q(SyntacticSubterm $L ($n + 1))) (β := q(SyntacticSubterm $L $n)) (dropFvar L n) arity v
    return q(func $f $v')
  | ~q(Operator.const $c)            => pure q(Operator.const $c)
  | ~q(Operator.operator (ι := Fin $arity) $f $v) => do
    let v' ← Qq.mapVector (α := q(SyntacticSubterm $L ($n + 1))) (β := q(SyntacticSubterm $L $n)) (dropFvar L n) arity v
    return q(Operator.operator $f $v')
  | ~q(substs (n := $l) $v $t)       => do
    let v' ← Qq.mapVector (α := q(SyntacticSubterm $L ($n + 1))) (β := q(SyntacticSubterm $L $n)) (dropFvar L n) l v
    return q(substs $v' $t)
  | ~q($t)                           => throwError m!"error in dropFvar: {t}"

/-
partial def unifyl (L : Q(Language.{u})) (n : ℕ) :
    (t : Q(SyntacticSubterm $L $n)) → (t' : Q(SyntacticSubterm $L $n)) →
    MetaM (List (Option Q(SyntacticSubterm $L $n)))
  | ~q($t),                              ~q(#$z)                => do
    let some z' := ←finQVal z | throwError m!"error in unifyl: {z}"
    return List.subtAt n z' t
  | ~q(func $f ![]),                      ~q(func $g ![])         => do
    if ←isDefEq f g
      then return List.replicate n none
      else throwError m!"unify failed: {f} =? {g}"
  | ~q(func $f ![$s]),                    ~q(func $g ![$t])       => do
    if ←isDefEq f g
      then unifyl L n s t
      else throwError m!"unify failed: {f} =? {g}"
  | ~q(func $f ![$s₁, $s₂]),              ~q(func $g ![$t₁, $t₂]) => do
    if ←isDefEq f g
      then return List.optCombine (←unifyl L n s₁ t₁) (←unifyl L n s₂ t₂)
      else throwError m!"unify failed: {f} =? {g}"
-- TODO: arity > 2
  | ~q(Operator.const $c₁),                ~q(Operator.const $c₂)              => do
    if ←isDefEq c₁ c₂ then
      return List.replicate n none
      else throwError m!"unify failed: {c₁} =? {c₂}"
  | ~q(Operator.operator $f ![]),         ~q(Operator.operator $g ![])         => do
    if ←isDefEq f g
      then return List.replicate n none
      else throwError m!"unify failed: {f} =? {g}"
  | ~q(Operator.operator $f ![$s]),       ~q(Operator.operator $g ![$t])       => do
    if ←isDefEq f g
      then unifyl L n s t
      else throwError m!"unify failed: {f} =? {g}"
  | ~q(Operator.operator $f ![$s₁, $s₂]), ~q(Operator.operator $g ![$t₁, $t₂]) => do
    if ←isDefEq f g
      then return List.optCombine (←unifyl L n s₁ t₁) (←unifyl L n s₂ t₂)
      else throwError m!"unify failed: {f} =? {g}"
  | ~q($s),                              ~q($t)                 => throwError m!"unify failed: {s} ⇝ {t}"

elab "dbgUnifyl" : term => do
  let L : Q(Language.{0}) := q(Language.oRing)
  let n := 3
  let t : Q(SyntacticSubterm $L 3) := q(ᵀ“0 + #1 + (&6 * 9 + 2)”)
  let t' : Q(SyntacticSubterm $L 3) := q(ᵀ“0 + #1 + (#0 + 2)”)
  let l ← unifyl L 3 t t'
  logInfo m!"subtVec: {l}"
  return t

#eval dbgUnifyl

end Meta

end Subterm

namespace Subformula

namespace Meta

open Subterm.Meta
variable {L : Q(Language.{u})} 
#check Operator.operator

partial def unifyl (L : Q(Language.{u})) (n : ℕ) :
    (p : Q(SyntacticSubformula $L $n)) → (p' : Q(SyntacticSubformula $L $n)) →
    MetaM (List (Option Q(SyntacticSubterm $L $n)))
  | ~q(⊤), ~q(⊤) => return List.replicate n none
  | ~q(⊥), ~q(⊥) => return List.replicate n none
  | ~q($p₁ ⋏ $p₂), ~q($q₁ ⋏ $q₂) => return List.optCombine (←unifyl L n p₁ q₁) (←unifyl L n p₂ q₂)
  | ~q($p₁ ⋎ $p₂), ~q($q₁ ⋎ $q₂) => return List.optCombine (←unifyl L n p₁ q₁) (←unifyl L n p₂ q₂)
  | ~q(∀' $p), ~q(∀' $q) => do
    let l ← unifyl L (n + 1) p q
    l.tail.mapM (·.mapM (dropFvar L n))
  | ~q(∃' $p),        ~q(∃' $q)        => do
    let l ← unifyl L (n + 1) p q
    l.tail.mapM (·.mapM (dropFvar L n))
  | ~q(rel $r ![]),         ~q(rel $q ![])         => 
    if ←isDefEq r q
      then return List.replicate n none
      else throwError m!"unify failed: {r} =? {q}"
  | ~q(rel $r ![$s]),       ~q(rel $q ![$t])       => 
    if ←isDefEq r q
      then Subterm.Meta.unifyl L n s t
      else throwError m!"unify failed: {r} =? {q}"
  | ~q(rel $r ![$s₁, $s₂]), ~q(rel $q ![$t₁, $t₂]) => 
    if ←isDefEq r q
      then return List.optCombine (←Subterm.Meta.unifyl L n s₁ t₁) (←Subterm.Meta.unifyl L n s₂ t₂)
      else throwError m!"unify failed: {r} =? {q}"
  | ~q(Operator.operator $r ![]),         ~q(Operator.operator $q ![])         => 
    if ←isDefEq r q
      then return List.replicate n none
      else throwError m!"unify failed: {r} =? {q}"
  | ~q(Operator.operator $r ![$s]),       ~q(Operator.operator $q ![$t])       => 
    if ←isDefEq r q
      then Subterm.Meta.unifyl L n s t
      else throwError m!"unify failed: {r} =? {q}"
  | ~q(Operator.operator $r ![$s₁, $s₂]), ~q(Operator.operator $q ![$t₁, $t₂]) => 
    if ←isDefEq r q
      then return List.optCombine (←Subterm.Meta.unifyl L n s₁ t₁) (←Subterm.Meta.unifyl L n s₂ t₂)
      else throwError m!"unify failed: {r} =? {q}"
  | ~q($p), ~q($q) => throwError m!"unify failed: {p} ⇝ {q}"

elab "dbgUnifyl₂" : term => do
  let L : Q(Language.{0}) := q(Language.oRing)
  let n := 3
  let p : Q(SyntacticSubformula $L 3) := q(“∀ (0 = #1)”)
  let p' : Q(SyntacticSubterm $L 3) := q(ᵀ“0 + #1 + (#0 + 2)”)
  let l ← unifyl L 3 t t'
  logInfo m!"subtVec: {l}"
  return t

#eval dbgUnifyl₂

end Meta

end Subformula

end FirstOrder

end LO
-/
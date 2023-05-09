import Logic.Predicate.FirstOrder.Meta
open Qq Lean Elab Meta Tactic Term

namespace SubTerm

namespace Meta

partial def findTerm {L : Q(Language.{u})} (s : Q(SyntacticTerm $L))
    (t : Q(SyntacticTerm $L)) : MetaM ((res : Q(SyntacticSubTerm $L 1)) × Q($t = substs ![$s] $res)) := do
  if (← isDefEq s t) then
    let eqn : Q($t = $s) := (q(@rfl (SyntacticTerm $L) $t) : Expr)
    return ⟨q(#0), q(eq_substs_zero_of_eq $eqn)⟩
  else
    match t with
    | ~q(&$x)                          => return ⟨q(&($x)), q(rfl)⟩
    | ~q(Operator.const $c)            => pure ⟨q(Operator.const $c), q(const_eq_substs_sonst_of_eq $c)⟩
    | ~q(func (arity := $arity) $f $v) =>
      let ⟨v', vh⟩ ← Qq.mapVectorInfo (u := u) (v := u) (H := q(fun t res => t = substs ![$s] res)) (findTerm s) arity v
      return ⟨q(func $f $v'), q(eq_substs_func_of_eq $f $vh)⟩
    | ~q(substs (n := $k) $v $t)       =>
      let ⟨v', vh⟩ ← Qq.mapVectorInfo (u := u) (v := u) (H := q(fun t res => t = substs ![$s] res)) (findTerm s) k v
      return ⟨q(substs $v' $t), q(eq_substs_substs_of_eq $t $vh)⟩
    | ~q($t)                           => do
      have v : Q(Fin 0 → SyntacticSubTerm $L 1) := q(![])
      let ⟨t', th⟩ ← resultSubsts (k := q(0)) (n := q(1)) v t
      return ⟨t', q(eq_substs_substs_nil $v $s $th)⟩

elab "dbgfindTerm" : term => do
  let L : Q(Language.{0}) := q(Language.oring)
  let t : Q(SyntacticTerm $L) := q(ᵀ“((&2 + 1) + 9) * (#0 + 1)ᵀ⟦&2 + 1, 6⟧ ”)
  logInfo m! "{t}"
  let s : Q(SyntacticTerm $L) := q(ᵀ“&2 + 1”)
  let v : Q(Fin 1 → SyntacticTerm $L) := q(![$s])
  let ⟨e, eq⟩ ← findTerm s t
  let dbgr := q(DbgResult.intro _ _ $eq)
  logInfo m! "{t} \n⟹ \n{e}"
  let ⟨e', eq'⟩ ← resultSubsts (u := levelZero) (L := L) (n := q(0)) v e
  logInfo m! "{e} \n⟹ \n{e'}"
  let dbgr' := q(DbgResult.intro _ _ $eq')
  return dbgr

#eval dbgfindTerm

end Meta

end SubTerm

namespace FirstOrder

namespace SubFormula

namespace Meta

partial def findFormula {L : Q(Language.{u})} (s : Q(SyntacticTerm $L)) :
    (p : Q(SyntacticFormula $L)) → MetaM ((res : Q(SyntacticSubFormula $L 1)) × Q($p = substs ![$s] $res))
  | ~q(⊤)        => return ⟨q(⊤), q(rfl)⟩
  | ~q(⊥)        => return ⟨q(⊥), q(rfl)⟩
  | ~q(rel (arity := $arity) $r $v)  => do
    let ⟨v', vh⟩ ← Qq.mapVectorInfo (u := u) (v := u) (H := q(fun t res => t = SubTerm.substs ![$s] res)) (SubTerm.Meta.findTerm s) arity v
    return ⟨q(rel $r $v'), q(rel_eq_substs_rel_of_eq $r $vh)⟩
  | ~q(nrel (arity := $arity) $r $v)  => do
    let ⟨v', vh⟩ ← Qq.mapVectorInfo (u := u) (v := u) (H := q(fun t res => t = SubTerm.substs ![$s] res)) (SubTerm.Meta.findTerm s) arity v
    return ⟨q(nrel $r $v'), q(nrel_eq_substs_nrel_of_eq $r $vh)⟩
  | ~q($p ⋏ $q)  => do
    let ⟨p', ph⟩ ← findFormula s p
    let ⟨q', qh⟩ ← findFormula s q
    return ⟨q($p' ⋏ $q'), q(eq_substs_and_of_eq $ph $qh)⟩
  | ~q($p ⋎ $q)  => do
    let ⟨p', ph⟩ ← findFormula s p
    let ⟨q', qh⟩ ← findFormula s q
    return ⟨q($p' ⋎ $q'), q(eq_substs_or_of_eq $ph $qh)⟩
  | ~q(∀' $p) => do
    let ⟨p', hp⟩ ← resultFree p
    let ⟨s', hs⟩ ← SubTerm.Meta.resultShift (u := u) (L := L) (n := q(0)) s
    let ⟨q, hq⟩ ← findFormula (L := L) s' p'
    let ⟨q', hq'⟩ ← resultFix (u := u) (L := L) q
    let ⟨q'', hq''⟩ ← resultSubsts (L := L) (n := q(2)) (k := q(2)) q(![#1, #0]) q'
    return ⟨q(∀' $q''), q(all_eq_substs_all_of_eq $hp $hs $hq $hq' $hq'')⟩
  | ~q(∃' $p) => do
    let ⟨p', hp⟩ ← resultFree p
    let ⟨s', hs⟩ ← SubTerm.Meta.resultShift (u := u) (L := L) (n := q(0)) s
    let ⟨q, hq⟩ ← findFormula (L := L) s' p'
    let ⟨q', hq'⟩ ← resultFix (u := u) (L := L) q
    let ⟨q'', hq''⟩ ← resultSubsts (L := L) (n := q(2)) (k := q(2)) q(![#1, #0]) q'
    return ⟨q(∃' $q''), q(ex_eq_substs_ex_of_eq $hp $hs $hq $hq' $hq'')⟩
  | ~q(~$p)  => do
    let ⟨p', ph⟩ ← findFormula s p
    return ⟨q(~$p'), q(eq_substs_neg_of_eq $ph)⟩
  | ~q($p ⟶ $q)  => do
    let ⟨p', ph⟩ ← findFormula s p
    let ⟨q', qh⟩ ← findFormula s q
    return ⟨q($p' ⟶ $q'), q(eq_substs_imply_of_eq $ph $qh)⟩
  | ~q($p ⟷ $q)  => do
    let ⟨p', ph⟩ ← findFormula s p
    let ⟨q', qh⟩ ← findFormula s q
    return ⟨q($p' ⟷ $q'), q(eq_substs_iff_of_eq $ph $qh)⟩
  | ~q(substs (n := $k) $v $p)       => do
    let ⟨v', vh⟩ ← Qq.mapVectorInfo (u := u) (v := u) (H := q(fun t res => t = SubTerm.substs ![$s] res)) (SubTerm.Meta.findTerm s) k v
    return ⟨q(substs $v' $p), q(eq_substs_substs_of_eq $p $vh)⟩
  | ~q($p)                           => do
    have v : Q(Fin 0 → SyntacticSubTerm $L 1) := q(![])
    let ⟨p', ph⟩ ← resultSubsts (k := q(0)) (n := q(1)) v p
    return ⟨p', q(eq_substs_substs_nil $v $s $ph)⟩
  

elab "dbgFindFormula" : term => do
  let L : Q(Language.{0}) := q(Language.oring)
  let p : Q(SyntacticFormula $L) := q(“∀ (&2 + 1) + 9 * (#0 + 1)ᵀ⟦&2 + 1, 6⟧ < 0”)
  let s : Q(SyntacticTerm $L) := q(ᵀ“&2 + 1”)
  let v : Q(Fin 1 → SyntacticTerm $L) := q(![$s])
  let ⟨e, eq⟩ ← findFormula s p
  let dbgr := q(DbgResult.intro _ _ $eq)
  logInfo m! "{p} \n⟹ \n{e}"
  return dbgr

#eval dbgFindFormula

end Meta

end SubFormula

end FirstOrder

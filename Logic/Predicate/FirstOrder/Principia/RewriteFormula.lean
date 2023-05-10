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

namespace Principia
open SubFormula
variable {L : Language.{u}}

inductive IffFormula : (p₀ q₀ : SyntacticFormula L) → SyntacticFormula L → SyntacticFormula L → Type u
  | intro {p₀ q₀} : IffFormula p₀ q₀ p₀ q₀
  | reflexivity {p₀ q₀} : (p : SyntacticFormula L) → IffFormula p₀ q₀ p p
  | and {p₀ q₀ p₁ p₂ q₁ q₂} : IffFormula p₀ q₀ p₁ q₁ → IffFormula p₀ q₀ p₂ q₂ → IffFormula p₀ q₀ (p₁ ⋏ p₂) (q₁ ⋏ q₂)
  | or {p₀ q₀ p₁ p₂ q₁ q₂} : IffFormula p₀ q₀ p₁ q₁ → IffFormula p₀ q₀ p₂ q₂ → IffFormula p₀ q₀ (p₁ ⋎ p₂) (q₁ ⋎ q₂)
  | all {p₀ q₀} {p q : SyntacticSubFormula L 1} : IffFormula (shift p₀) (shift q₀) (free p) (free q) → IffFormula p₀ q₀ (∀' p) (∀' q)
  | ex {p₀ q₀} {p q : SyntacticSubFormula L 1} : IffFormula (shift p₀) (shift q₀) (free p) (free q) → IffFormula p₀ q₀ (∃' p) (∃' q)
  | neg {p₀ q₀ p q} : IffFormula p₀ q₀ p q → IffFormula p₀ q₀ (~p) (~q)

namespace IffFormula
variable {p₀ q₀ : SyntacticFormula L}

def imply (h₁ : IffFormula p₀ q₀ p₁ q₁) (h₂ : IffFormula p₀ q₀ p₂ q₂) : IffFormula p₀ q₀ (p₁ ⟶ p₂) (q₁ ⟶ q₂) :=
  h₁.neg.or h₂

def iff (h₁ : IffFormula p₀ q₀ p₁ q₁) (h₂ : IffFormula p₀ q₀ p₂ q₂) : IffFormula p₀ q₀ (p₁ ⟷ p₂) (q₁ ⟷ q₂) :=
  (h₁.imply h₂).and (h₂.imply h₁)

def toStr : IffFormula p₀ q₀ p q → String := fun _ => "rr"

instance : ToString (IffFormula p₀ q₀ p q) := ⟨toStr⟩

end IffFormula

end Principia

namespace SubFormula
variable {L : Language.{u}}

namespace Meta
open Principia

section
variable {p₀ q₀ : SyntacticFormula L}

def IffFormula_of_eq {p} (h : p₀ = p) : IffFormula p₀ q₀ p q₀ := by rw[h]; exact IffFormula.intro

def IffFormula_all_of_eq (h : IffFormula p₀' q₀' p' q') (hp₀ : shift p₀ = p₀') (hq₀ : shift q₀ = q₀') (hp : free p = p') (hq : fix q' = q) :
    IffFormula p₀ q₀ (∀' p) (∀' q) := by simp[←hp₀, ←hq₀, ←hp] at h; exact IffFormula.all (by simpa[←hq])

def IffFormula_ex_of_eq (h : IffFormula p₀' q₀' p' q') (hp₀ : shift p₀ = p₀') (hq₀ : shift q₀ = q₀') (hp : free p = p') (hq : fix q' = q) :
    IffFormula p₀ q₀ (∃' p) (∃' q) := by simp[←hp₀, ←hq₀, ←hp] at h; exact IffFormula.ex (by simpa[←hq])


end

partial def rephraseFormula {L : Q(Language.{u})} (p₀ q₀ : Q(SyntacticFormula $L)) (p : Q(SyntacticFormula $L)) :
    MetaM ((res : Q(SyntacticFormula $L)) × Q(Principia.IffFormula $p₀ $q₀ $p $res)) := do
  if (← isDefEq p₀ p) then
    let eqn : Q($p₀ = $p) := (q(@rfl (SyntacticFormula $L) $p₀) : Expr)
    return ⟨q₀, q(IffFormula_of_eq $eqn)⟩
  else
    match p with
    | ~q(⊤) => return ⟨q(⊤), q(IffFormula.reflexivity _)⟩
    | ~q(⊥) => return ⟨q(⊥), q(IffFormula.reflexivity _)⟩
    | ~q($p ⋏ $q) => do
      let ⟨p₁, hp⟩ ← rephraseFormula p₀ q₀ p
      let ⟨q₁, hq⟩ ← rephraseFormula p₀ q₀ q
      return ⟨q($p₁ ⋏ $q₁), q(IffFormula.and $hp $hq)⟩
    | ~q($p ⋎ $q) => do
      let ⟨p₁, hp⟩ ← rephraseFormula p₀ q₀ p
      let ⟨q₁, hq⟩ ← rephraseFormula p₀ q₀ q
      return ⟨q($p₁ ⋎ $q₁), q(IffFormula.or $hp $hq)⟩
    | ~q(∀' $p) => do
      let ⟨p₀', hp₀⟩ ← resultShift (L := L) (n := q(0)) p₀
      let ⟨q₀', hq₀⟩ ← resultShift (L := L) (n := q(0)) q₀
      let ⟨p', hp⟩ ← resultFree (L := L) (n := q(0)) p
      let ⟨q', h⟩ ← rephraseFormula (L := L) p₀' q₀' p'
      let ⟨q, hq⟩ ← resultFix (L := L) (n := q(0)) q'
      return ⟨q(∀' $q), q(IffFormula_all_of_eq $h $hp₀ $hq₀ $hp $hq)⟩
    | ~q(∃' $p) => do
      let ⟨p₀', hp₀⟩ ← resultShift (L := L) (n := q(0)) p₀
      let ⟨q₀', hq₀⟩ ← resultShift (L := L) (n := q(0)) q₀
      let ⟨p', hp⟩ ← resultFree (L := L) (n := q(0)) p
      let ⟨q', h⟩ ← rephraseFormula (L := L) p₀' q₀' p'
      let ⟨q, hq⟩ ← resultFix (L := L) (n := q(0)) q'
      return ⟨q(∃' $q), q(IffFormula_ex_of_eq $h $hp₀ $hq₀ $hp $hq)⟩
    | ~q($p ⟶ $q) => do
      let ⟨p₁, hp⟩ ← rephraseFormula p₀ q₀ p
      let ⟨q₁, hq⟩ ← rephraseFormula p₀ q₀ q
      return ⟨q($p₁ ⟶ $q₁), q(IffFormula.imply $hp $hq)⟩
    | ~q($p ⟷ $q) => do
      let ⟨p₁, hp⟩ ← rephraseFormula p₀ q₀ p
      let ⟨q₁, hq⟩ ← rephraseFormula p₀ q₀ q
      return ⟨q($p₁ ⟷ $q₁), q(IffFormula.iff $hp $hq)⟩
    | ~q($p) => return ⟨p, q(IffFormula.reflexivity _)⟩

elab "rephraseFormula" : term => do
  let L : Q(Language.{0}) := q(Language.oring)
  let p₀ : Q(SyntacticFormula $L) := q(“&2 < 3”)
  let q₀ : Q(SyntacticFormula $L) := q(“&2 = 3”)
  let p : Q(SyntacticFormula $L) := q(“&2 < 3 → ∀ (&2 + 1) + 9 * (#0 + 1)ᵀ⟦&2 + 1, 6⟧ < 0”)

  let ⟨e, eq⟩ ← rephraseFormula p₀ q₀ p
  logInfo m! "{p} \n⟹ \n{e}"
  return eq

#eval rephraseFormula

end Meta

end SubFormula

end FirstOrder

import Logic.Predicate.FirstOrder.Basic
open Qq Lean Elab Meta Tactic Term

namespace LO

namespace FirstOrder

open Rew

namespace SubTerm

namespace Meta

lemma eq_substs_zero_of_eq {s t : Term L μ} (h : s = t) : s = substs ![t] #0 := by simp[h]

lemma const_eq_substs_sonst_of_eq (c : Const L) {s : Term L μ} : c.const = substs ![s] c.const := by simp

lemma eq_substs_func_of_eq {k} {s : Term L μ} (f : L.func k) {v : Fin k → Term L μ} {v' : Fin k → SubTerm L μ 1}
  (h : ∀ i, v i = substs ![s] (v' i)) : func f v = substs ![s] (func f v') := by simp[Rew.func, ←h]

lemma eq_substs_substs_of_eq {k} {s : Term L μ} (t : SubTerm L μ k) {v : Fin k → Term L μ} {v' : Fin k → SubTerm L μ 1}
  (h : ∀ i, v i = substs ![s] (v' i)) : substs v t = substs ![s] (substs v' t) := by
  have : v = (fun i => substs ![s] (v' i)) := by ext x; exact h x
  simp[this, ←Rew.comp_app]; congr; ext x <;> simp[Rew.comp_app]

lemma eq_substs_substs_nil (v) (s : Term L μ) {t : Term L μ} {t'} (ht : substs v t = t') :
  t = substs ![s] t' := by symm; simp[←ht, ←Rew.comp_app]; apply Rew.eq_id_of_eq <;> simp[Rew.comp_app]

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
      let ⟨v', vh⟩ ← Qq.vectorCollection (u := u) (v := u) (H := q(fun t res => t = substs ![$s] res)) (findTerm s) arity v
      return ⟨q(func $f $v'), q(eq_substs_func_of_eq $f $vh)⟩
    | ~q(substs (n := $k) $v $t')       =>
      let ⟨v', vh⟩ ← Qq.vectorCollection (u := u) (v := u) (H := q(fun t res => t = substs ![$s] res)) (findTerm s) k v
      return ⟨q(substs $v' $t'), q(eq_substs_substs_of_eq $t' $vh)⟩
    | ~q($t')                           => do
      have v : Q(Fin 0 → SyntacticSubTerm $L 1) := q(![])
      let ⟨t'', th⟩ ← resultSubsts L q(0) q(1) v t'
      return ⟨t'', q(eq_substs_substs_nil $v $s $th)⟩

elab "dbgfindTerm" : term => do
  let L : Q(Language.{0}) := q(Language.oRing)
  let t : Q(SyntacticTerm $L) := q(ᵀ“((&2 + 1) + 9) * (#0 + 1)ᵀ[&2 + 1, 6] ”)
  logInfo m! "{t}"
  let s : Q(SyntacticTerm $L) := q(ᵀ“&2 + 1”)
  let v : Q(Fin 1 → SyntacticTerm $L) := q(![$s])
  let ⟨e, eq⟩ ← findTerm s t
  let dbgr := q(DbgResult.intro _ _ $eq)
  logInfo m! "{t} \n⟹ \n{e}"
  let ⟨e', eq'⟩ ← resultSubsts L q(1) q(0) v e
  logInfo m! "{e} \n⟹ \n{e'}"
  let dbgr' := q(DbgResult.intro _ _ $eq')
  return dbgr

#eval dbgfindTerm

section lemmata
section 

variable {α : Type u}

lemma vec_concat_nth_tail {k} (x : α) (v : Fin k → α) (i : Fin k) (a : α) (h : v i = a) : (x :> v) (i.succ) = a := by
  simp[h]

lemma vec_concat_nth_head {k} (x : α) (v : Fin k → α) (a : α) (h : x = a) : (x :> v) 0 = a := by
  simp[h]

end

section Term
open SubTerm
variable {L : Language}

lemma subst_bvar (s : Fin k → SyntacticTerm L) (i : Fin k) (t : SyntacticTerm L) (h : s i = t) :
    t = substs s #i := by simp[h]

lemma substs_const' (s : Fin k → SyntacticTerm L) (c : Const L) : c.const = substs s c.const := by simp

lemma substs_func (s : Fin k → SyntacticTerm L) (f : L.func l) (v : Fin l → SyntacticTerm L) (v' : Fin l → SyntacticSubTerm L k)
  (h : ∀ i, v i = substs s (v' i)) : func f v = substs s (func f v') := by simp[Rew.func, ←h] 

lemma substs_substs (s : Fin k → SyntacticTerm L) (t : SyntacticSubTerm L arity)
  (v : Fin arity → SyntacticTerm L) (v' : Fin arity → SyntacticSubTerm L k)
  (h : ∀ i, v i = substs s (v' i)) : substs v t = substs s (substs v' t) := by
  have : v = (fun i => substs s (v' i)) := by ext x; exact h x
  simp[this, ←Rew.comp_app]; congr; ext x <;> simp[Rew.comp_app]

lemma substs_substs_nil  (s : Fin k → SyntacticTerm L) (v) (t : SyntacticTerm L) (t') (ht : substs v t = t') :
  t = substs s t' := by symm; simp[←ht, ←Rew.comp_app]; apply Rew.eq_id_of_eq <;> simp[Rew.comp_app]

end Term

end lemmata

#check Qq.vectorCollection
-- if s i = t then return some i else none
partial def findVecIndex {L : Q(Language.{u})} (k : Q(ℕ)) (s : Q(Fin $k → SyntacticTerm $L)) (t : Q(SyntacticTerm $L)) :
    MetaM $ Option $ (i : Q(Fin $k)) × Q($s $i = $t) := do
  match k with
  | ~q(0) => return none
  | ~q($k' + 1) =>
    let s : Q(Fin ($k' + 1) → SyntacticTerm $L) := s
    match s with
    | ~q($sh :> $st) =>
      match (←findVecIndex k' st t) with
      | some ⟨i, b⟩  =>
        let some ival := (← finQVal (n := q(.succ $k')) i) | throwError f!"Fail: FinQVal {i}"
        let z : Q(Fin ($k' + 1)) ← Lean.Expr.ofNat q(Fin ($k' + 1)) (ival + 1)
        return some ⟨z, (q(vec_concat_nth_tail $sh $st $i $t $b) : Expr)⟩
      | none =>
        if (←isDefEq sh t) then
          let eqn : Q($sh = $t) := (q(@rfl (SyntacticTerm $L) $t) : Expr)
          return some ⟨q(0), (q(vec_concat_nth_head $sh $st $t $eqn) : Expr)⟩
        else return none

partial def findTerms {L : Q(Language.{u})} (k : Q(ℕ)) (s : Q(Fin $k → SyntacticTerm $L))
    (t : Q(SyntacticTerm $L)) : MetaM ((res : Q(SyntacticSubTerm $L $k)) × Q($t = substs $s $res)) := do
  match (←findVecIndex k s t) with
  | some ⟨i, h⟩ =>
    return ⟨q(#$i), q(subst_bvar $s $i $t $h)⟩
  | none =>
    match t with
    | ~q(&$x)                          => return ⟨q(&($x)), q(rfl)⟩
    | ~q(Operator.const $c)            => pure ⟨q(Operator.const $c), q(substs_const' $s $c)⟩
    | ~q(func (arity := $arity) $f $v) =>
      let ⟨v', vh⟩ ← Qq.vectorCollection (u := u) (v := u) (H := q(fun t res => t = substs $s res)) (findTerms k s) arity v
      return ⟨q(func $f $v'), q(substs_func $s $f $v $v' $vh)⟩
    | ~q(substs (n := $arity) $v $t')       =>
      let ⟨v', vh⟩ ← Qq.vectorCollection (u := u) (v := u) (H := q(fun t res => t = substs $s res)) (findTerms k s) arity v
      return ⟨q(substs $v' $t'), q(substs_substs $s $t' $v $v' $vh)⟩
    | ~q($t')                           => do
      have v : Q(Fin 0 → SyntacticSubTerm $L $k) := q(![])
      let ⟨t'', th⟩ ← resultSubsts L q(0) k v t'
      return ⟨t'', q(substs_substs_nil $s $v $t' $t'' $th)⟩

elab "dbgfindTerms" : term => do
  let L : Q(Language.{0}) := q(Language.oRing)
  let t : Q(SyntacticTerm $L) := q(ᵀ“((&2 + 1) + 9*&3) * (#0 + 1)ᵀ[&2 + 1, 6] ”)
  logInfo m! "{t}"
  let s : Q(Fin 2 → SyntacticTerm $L) := q(![ᵀ“&2 + 1”, ᵀ“&3”])
  let ⟨e, eq⟩ ← findTerms q(2) s t
  let dbgr := q(DbgResult.intro _ _ $eq)
  logInfo m! "{t} \n⟹ \n{e}"
  let ⟨e', _⟩ ← resultSubsts L q(2) q(0) s e
  logInfo m! "{e} \n⟹ \n{e'}"
  return dbgr

#eval dbgfindTerms

end Meta

end SubTerm

namespace SubFormula

namespace Meta

section lemmata

lemma rel_eq_substs_rel_of_eq {k} {s : Term L μ} (r : L.rel k) {v : Fin k → Term L μ} {v' : Fin k → SubTerm L μ 1}
  (h : ∀ i, v i = [→ s] (v' i)) : rel r v = [→ s].hom (rel r v') := by simp[Rew.rel, ←h]

lemma nrel_eq_substs_nrel_of_eq {k} {s : Term L μ} (r : L.rel k) {v : Fin k → Term L μ} {v' : Fin k → SubTerm L μ 1}
  (h : ∀ i, v i = [→ s] (v' i)) : nrel r v = [→ s].hom (nrel r v') := by simp[Rew.nrel, ←h]

lemma eq_substs_and_of_eq {s : Term L μ} {p q : Formula L μ} {p' q' : SubFormula L μ 1}
  (hp : p = [→ s].hom p') (hq : q = [→ s].hom q') : p ⋏ q = [→ s].hom (p' ⋏ q') := by simp[←hp, ←hq]

lemma eq_substs_or_of_eq {s : Term L μ} {p q : Formula L μ} {p' q' : SubFormula L μ 1}
  (hp : p = [→ s].hom p') (hq : q = [→ s].hom q') : p ⋎ q = [→ s].hom (p' ⋎ q') := by simp[←hp, ←hq]

lemma all_eq_substs_all_of_eq {s : SyntacticTerm L} {s' p p' q q' q''}
  (hp : freel p = p') (hs : shift s = s') (findq : p' = [→ s'].hom q)
  (hq : fixl q = q') (hq' : [→ #1, #0].hom q' = q'') : ∀' p = [→ s].hom (∀' q'') := by
  have hp : p = fixl p' := by simpa using congr_arg fixl hp
  simp[hp, ←hs, findq, ←hq, ←hq', ←Rew.hom_comp_app]; apply Rew.hom_ext'
  ext x <;> simp[Fin.eq_zero, Matrix.empty_eq, Rew.comp_app]
  { have : (1 : Fin 2) = Fin.succ 0 := rfl; rw[this, q_bvar_succ]
    simp[←Rew.comp_app]; congr; ext x <;> simp[comp_app]; { exact Fin.elim0 x } }
  { cases x <;> simp }

lemma ex_eq_substs_ex_of_eq {s : SyntacticTerm L} {s' p p' q q' q''}
  (hp : freel p = p') (hs : shift s = s') (findq : p' = [→ s'].hom q)
  (hq : fixl q = q') (hq' : [→ #1, #0].hom q' = q'') : ∃' p = [→ s].hom (∃' q'') := by
  have hp : p = fixl p' := by simpa using congr_arg fixl hp
  simp[hp, ←hs, findq, ←hq, ←hq', ←Rew.hom_comp_app]; apply Rew.hom_ext'
  ext x <;> simp[Fin.eq_zero, Matrix.empty_eq, Rew.comp_app]
  { have : (1 : Fin 2) = Fin.succ 0 := rfl; rw[this, q_bvar_succ]
    simp[←Rew.comp_app]; congr; ext x <;> simp[comp_app]; { exact Fin.elim0 x } }
  { cases x <;> simp }

lemma operator_eq_substs_rel_of_eq {k} {s : Term L μ} (o : Operator L (Fin k)) {v : Fin k → Term L μ} {v' : Fin k → SubTerm L μ 1}
  (h : ∀ i, v i = [→ s] (v' i)) : o.operator v = [→ s].hom (o.operator v') := by simp[Operator.rew_operator, ←h]

lemma eq_substs_neg_of_eq {s : Term L μ} {p : Formula L μ} {p' : SubFormula L μ 1}
  (hp : p = [→ s].hom p') : ~p = [→ s].hom (~p') := by simp[←hp]

lemma eq_substs_imply_of_eq {s : Term L μ} {p q : Formula L μ} {p' q' : SubFormula L μ 1}
  (hp : p = [→ s].hom p') (hq : q = [→ s].hom q') :
    p ⟶ q = [→ s].hom (p' ⟶ q') := by simp[←hp, ←hq]

lemma eq_substs_iff_of_eq {s : Term L μ} {p q : Formula L μ} {p' q' : SubFormula L μ 1}
  (hp : p = [→ s].hom p') (hq : q = [→ s].hom q') :
    p ⟷ q = [→ s].hom (p' ⟷ q') := by simp[←hp, ←hq]

lemma eq_substs_substs_of_eq {k} {s : Term L μ} (p : SubFormula L μ k) {v : Fin k → Term L μ} {v' : Fin k → SubTerm L μ 1}
  (h : ∀ i, v i = substs ![s] (v' i)) : substsl v p = [→ s].hom (substsl v' p) := by
  have : v = (fun i => substs ![s] (v' i)) := by ext x; exact h x
  simp[this, ←hom_comp_app, substs_comp_substs, Function.comp]

lemma eq_substs_substs_nil (v) (s : Term L μ) {p : Formula L μ} {p'} (ht : substsl v p = p') :
  p = substsl ![s] p' := by simp[←ht, ←hom_comp_app, substs_comp_substs]

lemma univClosure_eq_of_eq' {n} {p : SubFormula L μ (n + 1)} {q} (h : univClosure (∀' p) = q) :
  univClosure p = q := by simp[←h]
  
end lemmata

partial def findFormula {L : Q(Language.{u})} (s : Q(SyntacticTerm $L)) :
    (p : Q(SyntacticFormula $L)) → MetaM ((res : Q(SyntacticSubFormula $L 1)) × Q($p = [→ $s].hom $res))
  | ~q(⊤)        => return ⟨q(⊤), q(Eq.symm $ LogicSymbol.HomClass.map_top _)⟩
  | ~q(⊥)        => return ⟨q(⊥), q(Eq.symm $ LogicSymbol.HomClass.map_bot _)⟩
  | ~q(rel (arity := $arity) $r $v)  => do
    let ⟨v', vh⟩ ← Qq.vectorCollection (u := u) (v := u) (H := q(fun t res => t = substs ![$s] res)) (SubTerm.Meta.findTerm s) arity v
    return ⟨q(rel $r $v'), q(rel_eq_substs_rel_of_eq $r $vh)⟩
  | ~q(nrel (arity := $arity) $r $v)  => do
    let ⟨v', vh⟩ ← Qq.vectorCollection (u := u) (v := u) (H := q(fun t res => t = substs ![$s] res)) (SubTerm.Meta.findTerm s) arity v
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
    let ⟨p', hp⟩ ← resultFree L q(0) p
    let ⟨s', hs⟩ ← SubTerm.Meta.resultShift (u := u) L q(0) s
    let ⟨q, hq⟩ ← findFormula (L := L) s' p'
    let ⟨q', hq'⟩ ← resultFix (u := u) L q(1) q
    let ⟨q'', hq''⟩ ← resultSubsts L q(2) q(2) q(![#1, #0]) q'
    return ⟨q(∀' $q''), q(all_eq_substs_all_of_eq $hp $hs $hq $hq' $hq'')⟩
  | ~q(∃' $p) => do
    let ⟨p', hp⟩ ← resultFree L q(0) p
    let ⟨s', hs⟩ ← SubTerm.Meta.resultShift (u := u) (L := L) (n := q(0)) s
    let ⟨q, hq⟩ ← findFormula (L := L) s' p'
    let ⟨q', hq'⟩ ← resultFix (u := u) L q(1) q
    let ⟨q'', hq''⟩ ← resultSubsts L q(2) q(2) q(![#1, #0]) q'
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
  | ~q(substsl (n := $k) $v $p)       => do
    let ⟨v', vh⟩ ← Qq.vectorCollection (u := u) (v := u) (H := q(fun t res => t = substs ![$s] res)) (SubTerm.Meta.findTerm s) k v
    return ⟨q(substsl $v' $p), q(eq_substs_substs_of_eq $p $vh)⟩
  | ~q(Operator.operator (ι := Fin $arity) $o $v) => do
    let ⟨v', vh⟩ ← Qq.vectorCollection (u := u) (v := u) (H := q(fun t res => t = substs ![$s] res)) (SubTerm.Meta.findTerm s) arity v
    return ⟨q(Operator.operator $o $v'), q(operator_eq_substs_rel_of_eq $o $vh)⟩
  | ~q($p)                           => do
    have v : Q(Fin 0 → SyntacticSubTerm $L 1) := q(![])
    let ⟨p', ph⟩ ← resultSubsts L (k := q(0)) (n := q(1)) v p
    return ⟨p', q(eq_substs_substs_nil $v $s $ph)⟩

elab "dbgFindFormula" : term => do
  let L : Q(Language.{0}) := q(Language.oRing)
  let p : Q(SyntacticFormula $L) := q(“∀ (&2 + 1) + 9 * (#0 + 1)ᵀ[&2 + 1, 6] < 0”)
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
  | all {p₀ q₀} {p q : SyntacticSubFormula L 1} : IffFormula (shiftl p₀) (shiftl q₀) (freel p) (freel q) → IffFormula p₀ q₀ (∀' p) (∀' q)
  | ex {p₀ q₀} {p q : SyntacticSubFormula L 1} : IffFormula (shiftl p₀) (shiftl q₀) (freel p) (freel q) → IffFormula p₀ q₀ (∃' p) (∃' q)
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

def IffFormula_all_of_eq (h : IffFormula p₀' q₀' p' q') (hp₀ : shiftl p₀ = p₀') (hq₀ : shiftl q₀ = q₀') (hp : freel p = p') (hq : fixl q' = q) :
    IffFormula p₀ q₀ (∀' p) (∀' q) := by simp[←hp₀, ←hq₀, ←hp] at h; exact IffFormula.all (by simpa[←hq])

def IffFormula_ex_of_eq (h : IffFormula p₀' q₀' p' q') (hp₀ : shiftl p₀ = p₀') (hq₀ : shiftl q₀ = q₀') (hp : freel p = p') (hq : fixl q' = q) :
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
  let L : Q(Language.{0}) := q(Language.oRing)
  let p₀ : Q(SyntacticFormula $L) := q(“&2 < 3”)
  let q₀ : Q(SyntacticFormula $L) := q(“&2 = 3”)
  let p : Q(SyntacticFormula $L) := q(“&2 < 3 → ∀ (&2 + 1) + 9 * (#0 + 1)ᵀ[&2 + 1, 6] < 0”)
  let ⟨e, eq⟩ ← rephraseFormula p₀ q₀ p
  logInfo m! "{p} \n⟹ \n{e}"
  return eq

#eval rephraseFormula

end Meta

end SubFormula

namespace SubTerm

namespace Meta

def fvarStr (s : String) : Option ℕ :=
  if s = "var₀" then some 0
  else if s = "var₁" then some 1
  else if s = "var₂" then some 2
  else if s = "var₃" then some 3
  else if s = "var₄" then some 4
  else none

partial def strToSyntactic (s : List String) (L : Q(Language.{u})) (n : Q(ℕ)) : Q(SubTerm $L String $n) → MetaM (Q(SyntacticSubTerm $L $n))
  | ~q(#$x)                          => pure q(#$x)
  | ~q(&$x)                          => do 
    let some x := Lean.Expr.stringLit? (←whnf x) | throwError "not String"
    let (z : Q(ℕ)) ← match fvarStr x with
      | some i => Expr.ofNat q(ℕ) i
      | none =>
        let i := s.indexOf x
        if i = s.length then
          throwError m!"variable {x} was not declared"
        else
          Expr.ofNat q(ℕ) i
      return q(&$z)
  | ~q(func (arity := $arity) $f $v) => do
  let v' ← mapVector (u := u) (v := u) (strToSyntactic s L n) arity v
  return q(func $f $v')
  | ~q(substs (n := $k) $w $t)       => do
    let t' ← strToSyntactic s L k t
    let w' ← mapVector (u := u) (v := u) (strToSyntactic s L n) k w
    return q(substs $w' $t')
  | ~q(Operator.const $c)            => pure q(Operator.const $c)
  | ~q(Operator.operator (ι := Fin $arity) $f $v) => do
    let v' ← mapVector (u := u) (v := u) (strToSyntactic s L n) arity v
    return q(Operator.operator $f $v')
  | ~q($t)                           => throwError m!"non-exhaustive match: {t}"

elab "dbgstrToSyntactic" : term => do
  let s : List String := ["x₁", "x₂", "a₁"]
  let L : Q(Language.{0}) := q(Language.oRing)
  let t : Q(SubTerm $L String 2) := q(ᵀ“4 + x₂ * var₂”)
  let t' ← strToSyntactic s L q(2) t
  logInfo m! "{t} \n⟹ \n{t'}"
  return t

#eval dbgstrToSyntactic

partial def syntacticToStr (s : List String) (L : Q(Language.{u})) (n : Q(ℕ)) : Q(SyntacticSubTerm $L $n) → MetaM (Q(SubTerm $L String $n))
  | ~q(#$x)                          => pure q(#$x)
  | ~q(&$x)                          => do 
    let some x := Lean.Expr.natLit? (←whnf x) | throwError "not ℕ"
    let (z : String) := match s.get? x with
      | some s => s
      | none => "var_not_found"
    return q(&$z)
  | ~q(func (arity := $arity) $f $v) => do
  let v' ← mapVector (u := u) (v := u) (syntacticToStr s L n) arity v
  return q(func $f $v')
  | ~q(substs (n := $k) $w $t)       => do
    let t' ← syntacticToStr s L k t
    let w' ← mapVector (u := u) (v := u) (syntacticToStr s L n) k w
    return q(substs $w' $t')
  | ~q(Operator.const $c)            => pure q(Operator.const $c)
  | ~q(Operator.operator (ι := Fin $arity) $f $v) => do
    let v' ← mapVector (u := u) (v := u) (syntacticToStr s L n) arity v
    return q(Operator.operator $f $v')
  | ~q($t)                           => throwError m!"non-exhaustive match: {t}"

elab "dbgsyntacticToStr" : term => do
  let s : List String := ["x₁", "x₂", "a₁"]
  let L : Q(Language.{0}) := q(Language.oRing)
  let t : Q(SyntacticSubTerm $L 2) := q(ᵀ“4 + &1”)
  let t' ← syntacticToStr s L q(2) t
  logInfo m! "{t} \n⟹ \n{t'}"
  return t

#eval dbgsyntacticToStr

end Meta

end SubTerm

namespace SubFormula

namespace Meta

partial def strToSyntactic (s : List String) (L : Q(Language.{u})) (n : Q(ℕ)) : (p : Q(SubFormula $L String $n)) →
    MetaM Q(SyntacticSubFormula $L $n)
  | ~q(⊤)                            => pure q(⊤)
  | ~q(⊥)                            => pure q(⊥)
  | ~q(rel (arity := $arity) $r $v)  => do
    let v' ← mapVector (u := u) (v := u) (SubTerm.Meta.strToSyntactic s L n) arity v
    return q(rel $r $v')
  | ~q(nrel (arity := $arity) $r $v) => do
    let v' ← mapVector (u := u) (v := u) (SubTerm.Meta.strToSyntactic s L n) arity v
    return q(nrel $r $v')
  | ~q($p ⋏ $q)                      => do
    let pn ← strToSyntactic s L n p
    let qn ← strToSyntactic s L n q
    return q($pn ⋏ $qn)
  | ~q($p ⋎ $q)                      => do
    let pn ← strToSyntactic s L n p
    let qn ← strToSyntactic s L n q
    return q($pn ⋎ $qn)
  | ~q(∀' $p)                        => do
    let pn ← strToSyntactic s L q($n + 1) p
    return q(∀' $pn)
  | ~q(∃' $p)                        => do
    let pn ← strToSyntactic s L q($n + 1) p
    return q(∃' $pn)
  | ~q(~$p)                          => do
    let pn ← strToSyntactic s L n p
    return q(~$pn)
  | ~q($p ⟶ $q)                      => do
    let pn ← strToSyntactic s L n p
    let qn ← strToSyntactic s L n q
    return q($pn ⟶ $qn)
  | ~q($p ⟷ $q)                      => do
    let pn ← strToSyntactic s L n p
    let qn ← strToSyntactic s L n q
    return q($pn ⟷ $qn)
  | ~q(∀[$p] $q)                     => do
    let p' ← strToSyntactic s L q($n + 1) p
    let q' ← strToSyntactic s L q($n + 1) q
    return q(∀[$p'] $q')
  | ~q(∃[$p] $q)                     => do
    let p' ← strToSyntactic s L q($n + 1) p
    let q' ← strToSyntactic s L q($n + 1) q
    return q(∃[$p'] $q')
  | ~q(Rew.substsl (n := $k) $w $p)       => do
    let w' ← mapVector (u := u) (v := u) (SubTerm.Meta.strToSyntactic s L n) k w
    let p' ← strToSyntactic s L k p
    return q(Rew.substsl $w' $p')
  | ~q(Operator.operator (ι := Fin $arity) $o $v) => do
    let v' ← mapVector (u := u) (v := u) (SubTerm.Meta.strToSyntactic s L n) arity v
    return q(Operator.operator $o $v')
  | ~q($p)                           => throwError m!"non-exhaustive match: {p}"

elab "dbgstrToSyntactic'" : term => do
  let s : List String := ["x", "y", "z", "x₁", "x₂", "a₁"]
  let L : Q(Language.{0}) := q(Language.oRing)
  let p : Q(SubFormula $L String 2) := q(“x + 4 < x₁ + x₂ → ∀ (#0 + y = 5)”)
  let p' ← strToSyntactic s L q(2) p
  logInfo m! "{p} \n⟹ \n{p'}"
  return p

#eval dbgstrToSyntactic'

partial def syntacticToStr (s : List String) (L : Q(Language.{u})) (n : Q(ℕ)) : (p : Q(SyntacticSubFormula $L $n)) →
    MetaM Q(SubFormula $L String $n)
  | ~q(⊤)                            => pure q(⊤)
  | ~q(⊥)                            => pure q(⊥)
  | ~q(rel (arity := $arity) $r $v)  => do
    let v' ← mapVector (u := u) (v := u) (SubTerm.Meta.syntacticToStr s L n) arity v
    return q(rel $r $v')
  | ~q(nrel (arity := $arity) $r $v) => do
    let v' ← mapVector (u := u) (v := u) (SubTerm.Meta.syntacticToStr s L n) arity v
    return q(nrel $r $v')
  | ~q($p ⋏ $q)                      => do
    let pn ← syntacticToStr s L n p
    let qn ← syntacticToStr s L n q
    return q($pn ⋏ $qn)
  | ~q($p ⋎ $q)                      => do
    let pn ← syntacticToStr s L n p
    let qn ← syntacticToStr s L n q
    return q($pn ⋎ $qn)
  | ~q(∀' $p)                        => do
    let pn ← syntacticToStr s L q($n + 1) p
    return q(∀' $pn)
  | ~q(∃' $p)                        => do
    let pn ← syntacticToStr s L q($n + 1) p
    return q(∃' $pn)
  | ~q(~$p)                          => do
    let pn ← syntacticToStr s L n p
    return q(~$pn)
  | ~q($p ⟶ $q)                      => do
    let pn ← syntacticToStr s L n p
    let qn ← syntacticToStr s L n q
    return q($pn ⟶ $qn)
  | ~q($p ⟷ $q)                      => do
    let pn ← syntacticToStr s L n p
    let qn ← syntacticToStr s L n q
    return q($pn ⟷ $qn)
  | ~q(∀[$p] $q)                     => do
    let p' ← syntacticToStr s L q($n + 1) p
    let q' ← syntacticToStr s L q($n + 1) q
    return q(∀[$p'] $q')
  | ~q(∃[$p] $q)                     => do
    let p' ← syntacticToStr s L q($n + 1) p
    let q' ← syntacticToStr s L q($n + 1) q
    return q(∃[$p'] $q')
  | ~q(Rew.substsl (n := $k) $w $p)       => do
    let w' ← mapVector (u := u) (v := u) (SubTerm.Meta.syntacticToStr s L n) k w
    let p' ← syntacticToStr s L k p
    return q(Rew.substsl $w' $p')
  | ~q(Operator.operator (ι := Fin $arity) $o $v) => do
    let v' ← mapVector (u := u) (v := u) (SubTerm.Meta.syntacticToStr s L n) arity v
    return q(Operator.operator $o $v')
  | ~q($p)                           => throwError m!"non-exhaustive match: {p}"

end Meta

end SubFormula

end FirstOrder

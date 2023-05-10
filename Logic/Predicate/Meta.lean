import Logic.Predicate.Coding
import Logic.Vorspiel.Meta
open Qq Lean Elab Meta Tactic

-- SubTerm normalization
namespace SubTerm

namespace Meta

section lemmata
variable {L : Language.{u}} {μ : Type v} {n}

section substs

lemma substs_bvar_of_eq {n n'} {w : Fin n → SubTerm L μ n'} {x : Fin n} {t} (h : w x = t) :
    substs w #x = t :=
  by simp[h]

lemma substs_func_of_eq {n n'} {w : Fin n → SubTerm L μ n'} {k} (f : L.func k) {v : Fin k → SubTerm L μ n} {v'} (h : substs w ∘ v = v') :
    substs w (func f v) = func f v' :=
  by simp[substs_func, Function.comp, ←h]

lemma substs_substs_of_eq {l k n} {v : Fin l → SubTerm L μ k} {w : Fin k → SubTerm L μ n}
  {t : SubTerm L μ l} {v'} {t'}
  (hv : substs w ∘ v = v') (ht : substs v' t = t') :
    substs w (substs v t) = t' := by simp[substs_substs, ←hv, ←ht]

lemma substs_eq_of_eq {k n} {w w' : Fin k → SubTerm L μ n} {t t' : SubTerm L μ k} {u}
  (hw : w = w') (ht : t = t') (h : substs w' t' = u) : substs w t = u := hw ▸ ht ▸ h

lemma substs_finitary_of_eq {n n'} {w : Fin n → SubTerm L μ n'} {k} (f : Finitary L k) {v : Fin k → SubTerm L μ n} {v'} (h : substs w ∘ v = v') :
    substs w (f.operator v) = f.operator v' :=
  by simp[Operator.substs_operator, Function.comp, ←h]

end substs

section shift

lemma shift_func_of_eq {n} (f : L.func k) {v : Fin k → SyntacticSubTerm L n} {v'} (h : shift ∘ v = v') :
    shift (func f v) = func f v' :=
  by simp[shift_func, Function.comp, ←h]

lemma shift_substs_of_eq {t : SyntacticSubTerm L k} {w : Fin k → SyntacticSubTerm L n} {t' t'' w'}
  (ht : shift t = t') (hw : shift ∘ w = w') (ht' : substs w' t' = t'') :
    shift (substs w t) = t'' := by
  simp[←ht, ←hw, ←ht', shift, substs, map, bind_bind]

lemma shift_finitary_of_eq {n} (f : Finitary L k) {v : Fin k → SyntacticSubTerm L n} {v'} (h : shift ∘ v = v') :
    shift (f.operator v) = f.operator v' :=
  by simp[Operator.shift_operator, Function.comp, ←h]

end shift

section bShift

lemma bShift_func_of_eq (f : L.func k) {v : Fin k → SubTerm L μ n} {v'} (h : bShift ∘ v = v'):
    bShift (func f v) = func f v' := by simp[←h, bShift_func]; funext x; simp

lemma bShift_substs_of_eq {w : Fin k → SubTerm L μ n} {t : SubTerm L μ k} {w' t'}
  (hw : bShift ∘ w = w') (ht : substs w' t = t') :
    bShift (substs w t) = t' := by
  simp[←hw, ←ht, bShift, substs, map, bind_bind]; congr

lemma bShift_finitary_of_eq (f : Finitary L k) {v : Fin k → SubTerm L μ n} {v'} (h : bShift ∘ v = v'):
    bShift (f.operator v) = f.operator v' := by simp[←h, Operator.bShift_operator f v, Function.comp]

end bShift

section free

lemma free_bvar_last (n : ℕ) : free (#⟨n, Nat.lt.base n⟩ : SyntacticSubTerm L (n + 1)) = &0 :=
  SubTerm.free_bvar_last

lemma free_bvar_of_lt (x : Fin (n + 1)) (h : x.val < n) : free (#x : SyntacticSubTerm L (n + 1)) = #⟨x, h⟩ :=
  free_bvar_castSucc (L := L) ⟨x, h⟩

lemma free_func_of_eq {n} (f : L.func k) {v : Fin k → SyntacticSubTerm L (n + 1)} {v'} (h : free ∘ v = v') :
    free (func f v) = func f v' :=
  by simp[free_func, Function.comp, ←h]

lemma free_substs_of_eq {t : SyntacticSubTerm L k} {w : Fin k → SyntacticSubTerm L (n + 1)} {t' w' t''}
  (ht : shift t = t') (hw : free ∘ w = w') (ht' : substs w' t' = t'') :
    free (substs w t) = t'' := by
  simp[←ht, ←hw, ←ht', shift, map, free, substs, bind_bind]

lemma free_finitary_of_eq {n} (f : Finitary L k) {v : Fin k → SyntacticSubTerm L (n + 1)} {v'} (h : free ∘ v = v') :
    free (f.operator v) = f.operator v' :=
  by simp[Operator.free_operator, Function.comp, ←h]

end free

section fix

lemma fix_fvar (x) : fix (#x : SyntacticSubTerm L n) = #(.castSucc x) :=
  SubTerm.fix_bvar x

lemma fix_bvar_zero (n : ℕ) : fix &0 = (#⟨n, Nat.lt.base n⟩ : SyntacticSubTerm L (n + 1)) :=
  SubTerm.fix_fvar_zero

lemma fix_bvar_succ (x) (n : ℕ) : fix (&(x + 1) : SyntacticSubTerm L (n + 1)) = &x :=
  SubTerm.fix_fvar_succ x

lemma fix_func_of_eq {n} (f : L.func k) {v : Fin k → SyntacticSubTerm L n} {v'} (h : fix ∘ v = v') :
    fix (func f v) = func f v' :=
  by simp[fix_func, Function.comp, ←h]

lemma fix_substs_of_eq {k} {t : SyntacticSubTerm L k} {w : Fin k → SyntacticSubTerm L n} {t' t'' w' w'' i}
  (ht : fix t = t') (hw : fix ∘ w = w') (hi : Fin.last n = i) (hw' : w' <: #i = w'') (ht' : substs w'' t' = t''):
    fix (substs w t) = t'' := by
  simp[←ht, ←hw, ←hi, ←hw', ←ht', shift, map, fix, substs, bind_bind, Function.comp]; congr
  · funext x; cases x <;> simp

lemma fix_finitary_of_eq {n} (f : Finitary L k) {v : Fin k → SyntacticSubTerm L n} {v'} (h : fix ∘ v = v') :
    fix (f.operator v) = f.operator v' :=
  by simp[Operator.fix_operator, Function.comp, ←h]

end fix

lemma func_congr  {k} (f : L.func k) {v₁ v₂ : Fin k → SyntacticSubTerm L n} (h : v₁ = v₂):
    func f v₁ = func f v₂ := by simp[←h]

lemma finitary_congr  {k} (f : Finitary L k) {v₁ v₂ : Fin k → SyntacticSubTerm L n} (h : v₁ = v₂):
    f.operator v₁ = f.operator v₂ := by simp[←h]

lemma free_congr_eq {t t' : SyntacticSubTerm L (n + 1)} {s} (e : t = t') (h : free t' = s) :
  free t = s := Eq.trans (congr_arg _ e) h

lemma shift_congr_eq {t t' : SyntacticSubTerm L n} {u} (e : t = t') (h : shift t' = u) :
  shift t = u := Eq.trans (congr_arg _ e) h

lemma bShift_congr_eq {t t' : SubTerm L μ n} {u} (e : t = t') (h : bShift t' = u) :
  bShift t = u := Eq.trans (congr_arg _ e) h

section
variable (c : Const L)

@[simp] lemma free_const :
    free (c : SyntacticSubTerm L (n + 1)) = c :=
  by simp

@[simp] lemma fix_const :
    fix (c : SyntacticSubTerm L n) = c :=
  by simp

@[simp] lemma substs_const {n'} {w : Fin n → SubTerm L μ n'} :
    substs w (c : SubTerm L μ n) = c :=
  by simp

@[simp] lemma shift_const :
    shift (c : SyntacticSubTerm L n) = c :=
  by simp

@[simp] lemma bShift_const :
    bShift (c : SubTerm L μ n) = c :=
  by simp[bShift]

variable [L.Zero] [L.One] [L.Add]

lemma natLit_succ_of_eq {z : ℕ} (t : SubTerm L μ n) (h : natLit L z.succ = t) :
  natLit L z.succ.succ = func Language.Add.add ![t, func Language.One.one ![]] := by rw[←h]; rfl

end

lemma eq_substs_zero_of_eq {s t : Term L μ} (h : s = t) : s = substs ![t] #0 := by simp[h]

lemma const_eq_substs_sonst_of_eq (c : Const L) {s : Term L μ} : c.const = substs ![s] c.const := by simp

lemma eq_substs_func_of_eq {k} {s : Term L μ} (f : L.func k) {v : Fin k → Term L μ} {v' : Fin k → SubTerm L μ 1}
  (h : ∀ i, v i = substs ![s] (v' i)) : func f v = substs ![s] (func f v') := by simp[substs_func, ←h]

lemma eq_substs_substs_of_eq {k} {s : Term L μ} (t : SubTerm L μ k) {v : Fin k → Term L μ} {v' : Fin k → SubTerm L μ 1}
  (h : ∀ i, v i = substs ![s] (v' i)) : substs v t = substs ![s] (substs v' t) := by simp[substs_substs, Function.comp, ←h]

lemma eq_substs_substs_nil (v) (s : Term L μ) {t : Term L μ} {t'} (ht : substs v t = t') :
  t = substs ![s] t' := by simp[←ht, substs_substs]

end lemmata

partial def resultSubsts {L : Q(Language.{u})} {k n : Q(ℕ)} (w : Q(Fin $k → SyntacticSubTerm $L $n)) :
    (t : Q(SyntacticSubTerm $L $k)) → MetaM ((res : Q(SyntacticSubTerm $L $n)) × Q(substs $w $t = $res))
  | ~q(#$x)                          => do
    let ⟨t, ht⟩ ← vectorQNth (u := u) k w x
    return ⟨t, q(substs_bvar_of_eq $ht)⟩
  | ~q(&$x)                          => pure ⟨q(&$x), q(substs_fvar $w $x)⟩
  | ~q(func (arity := $arity) $f $v) => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L $k)) (β := q(SyntacticSubTerm $L $n))
      q(substs $w) (resultSubsts w) arity v
    return ⟨q(func $f $v'), q(substs_func_of_eq $f $ve)⟩
  | ~q(Operator.const $c)            => pure ⟨q(Operator.const $c), q(substs_const $c)⟩
  | ~q(Operator.operator (ι := Fin $arity) $f $v) => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L $k)) (β := q(SyntacticSubTerm $L $n))
      q(substs $w) (resultSubsts w) arity v
    return ⟨q(Operator.operator $f $v'), q(substs_finitary_of_eq $f $ve)⟩
  | ~q(substs (n := $l) $v $t)       => do
    let ⟨v', ve⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L $k)) (β := q(SyntacticSubTerm $L $n))
      q(@SubTerm.substs $L ℕ $k $n $w) (resultSubsts w) l v
    let ⟨p', pe⟩ ← resultSubsts v' t
    return ⟨p', q(substs_substs_of_eq $ve $pe)⟩
  | ~q($t)                           => pure ⟨q(substs $w $t), q(rfl)⟩

partial def resultShift {L : Q(Language.{u})} {n : Q(ℕ)} : (t : Q(SyntacticSubTerm $L $n)) →
    MetaM ((res : Q(SyntacticSubTerm $L $n)) × Q(SubTerm.shift $t = $res))
  | ~q(#$x)                          => pure ⟨q(#$x), q(SubTerm.shift_bvar $x)⟩
  | ~q(&$x)                          =>  do
    let z ← natAppFunQ Nat.succ x
    let e := q(SubTerm.shift_fvar (L := $L) (n := $n) $x)
    return ⟨q(&$z), e⟩
  | ~q(func (arity := $arity) $f $v) => do
    let ⟨v', ve'⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L $n))
      q(@shift $L $n) resultShift arity v
    return ⟨q(func $f $v'), q(shift_func_of_eq $f $ve')⟩
  | ~q(substs (n := $k) $w $t)       => do
    let ⟨t', te⟩ ← resultShift (L := L) (n := k) t
    let ⟨w', we⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L $n))
      q(@SubTerm.shift $L $n) resultShift k w
    let ⟨t'', t'e⟩ ← resultSubsts w' t'
    return ⟨t'', q(shift_substs_of_eq $te $we $t'e)⟩
  | ~q(SubTerm.Operator.const $c)    => pure ⟨q(SubTerm.Operator.const $c), q(shift_const $c)⟩
  | ~q(Operator.operator (ι := Fin $arity) $f $v) => do
    let ⟨v', ve'⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L $n))
      q(@shift $L $n) resultShift arity v
    return ⟨q(Operator.operator $f $v'), q(shift_finitary_of_eq $f $ve')⟩
  | ~q($t)                           => do
    return ⟨q(shift $t), q(rfl)⟩

partial def resultFree {L : Q(Language.{u})} {n : Q(ℕ)} : (t : Q(SyntacticSubTerm $L ($n + 1))) →
    MetaM ((res : Q(SyntacticSubTerm $L $n)) × Q(SubTerm.free $t = $res))
  | ~q(#$x)                                       => do
    let n ←whnf n 
    let some nval := n.natLit? | throwError f!"Fail: natLit: {n}"
    let some xval := (← finQVal (n := q(.succ $n)) x) | throwError f!"Fail: FinQVal {x}"
    if xval = nval then
      let e := q(free_bvar_last (L := $L) $n)
      return ⟨q(&0), e⟩
    else
      let lt ← decideTQ q(($x).val < $n)
      let e := q(free_bvar_of_lt (L := $L) $x $lt)
      let z : Q(Fin $n) ← Lean.Expr.ofNat q(Fin $n) xval
      return ⟨q(#$z), e⟩
  | ~q(&$x)                                       => do
    let z ← natAppFunQ Nat.succ x
    let e : Expr := q(SubTerm.free_fvar (L := $L) (n := $n) $x)
    return ⟨q(&$z), e⟩
  | ~q(func (arity := $arity) $f $v)              => do
    let ⟨v', ve'⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L ($n + 1))) (β := q(SyntacticSubTerm $L $n))
      q(@free $L $n) resultFree arity v
    return ⟨q(func $f $v'), q(free_func_of_eq $f $ve')⟩
  | ~q(substs (n := $k) $w $t)                    => do
    let ⟨t', te⟩ ← resultShift (L := L) (n := k) t
    let ⟨w', we⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L ($n + 1))) (β := q(SyntacticSubTerm $L $n))
      q(@SubTerm.free $L $n) resultFree k w
    let ⟨t'', t'e⟩ ← resultSubsts w' t'
    return ⟨t'', q(free_substs_of_eq $te $we $t'e)⟩
  | ~q(SubTerm.Operator.const $c)                 => return ⟨q(SubTerm.Operator.const $c), q(free_const _)⟩
  | ~q(Operator.operator (ι := Fin $arity) $f $v) => do
    let ⟨v', ve'⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L ($n + 1))) (β := q(SyntacticSubTerm $L $n))
      q(@free $L $n) resultFree arity v
    return ⟨q(Operator.operator $f $v'), q(free_finitary_of_eq $f $ve')⟩
  | ~q($t)                                        => do
    return ⟨q(SubTerm.free $t), q(rfl)⟩

#check fix_substs_of_eq

partial def resultFix {L : Q(Language.{u})} {n : Q(ℕ)} : (t : Q(SyntacticSubTerm $L $n)) →
    MetaM ((res : Q(SyntacticSubTerm $L ($n + 1))) × Q(SubTerm.fix $t = $res))
  | ~q(#$x)                                       => do
    let some xval := (← finQVal (n := q(.succ $n)) x) | throwError f!"Fail: FinQVal {x}"
    let e : Expr := q(SubTerm.fix_bvar (L := $L) (n := $n) $x)
    let z : Q(Fin ($n + 1)) ← Lean.Expr.ofNat q(Fin ($n + 1)) xval
    return ⟨q(#$z), e⟩
  | ~q(&0)                                        => do
    let n' ←whnf n 
    let some nval := n'.natLit? | throwError f!"Fail: natLit: {n}"
    let z : Q(Fin ($n + 1)) ← Lean.Expr.ofNat q(Fin ($n + 1)) nval
    let hh := q(@fix_bvar_zero $L $n)
    return ⟨q(#$z), hh⟩
  | ~q(&($x + 1))                                 => do
    return ⟨q(&$x), q(SubTerm.fix_fvar_succ (L := $L) (n := $n) $x)⟩
  | ~q(func (arity := $arity) $f $v)              => do
    let ⟨v', ve'⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L ($n + 1)))
      q(@fix $L $n) resultFix arity v
    return ⟨q(func $f $v'), q(fix_func_of_eq $f $ve')⟩
  | ~q(substs (n := $k) $w $t)                    => do
    let ⟨t', ht⟩ ← resultFix (L := L) (n := k) t
    let ⟨w', hw⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L ($n + 1)))
      q(@fix $L $n) resultFix k w
    let some nval := (←whnf n).natLit? | throwError f!"Fail: natLit: {n}"
    let z : Q(Fin ($n + 1)) ← Lean.Expr.ofNat q(Fin ($n + 1)) nval
    let hz : Q(Fin.last $n = $z) := (q(@rfl (Fin ($n + 1)) $z) : Expr)
    let ⟨w'', hw'⟩ ← vectorAppend k w' q(#$z)
    let ⟨t'', ht'⟩ ← resultSubsts w'' t'
    return ⟨t'', q(fix_substs_of_eq $ht $hw $hz $hw' $ht')⟩
  | ~q(SubTerm.Operator.const $c)                 => return ⟨q(SubTerm.Operator.const $c), q(fix_const _)⟩
  | ~q(Operator.operator (ι := Fin $arity) $f $v) => do
    let ⟨v', ve'⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L ($n + 1)))
      q(@fix $L $n) resultFix arity v
    return ⟨q(Operator.operator $f $v'), q(fix_finitary_of_eq $f $ve')⟩
  | ~q($t)                                        => do
    return ⟨q(SubTerm.fix $t), q(rfl)⟩

elab "dbgResultFix" : term => do
  let L : Q(Language.{0}) := q(Language.oring)
  let t : Q(SyntacticTerm $L) := q(ᵀ“((&2 + 1) + 9) * (#0 + 1)ᵀ⟦&2 + 1, 6⟧ ”)
  let ⟨e, eq⟩ ← resultFix (L := L) (n := q(0)) t
  logInfo m! "{t}\n ⟹\n {e}"
  let dbgr := q(DbgResult.intro _ _ $eq)
  return dbgr

#eval dbgResultFix

partial def resultBShift {L : Q(Language.{u})} {n : Q(ℕ)} : (t : Q(SyntacticSubTerm $L $n)) →
    MetaM ((res : Q(SyntacticSubTerm $L ($n + 1))) × Q(bShift $t = $res))
  | ~q(#$x)                                       => do
    let some xval := (← finQVal (n := q(.succ $n)) x) | throwError f!"Fail: FinQVal {x}"
    let z : Q(Fin ($n + 1)) ← Lean.Expr.ofNat q(Fin ($n + 1)) (xval + 1)
    let e := q(SubTerm.bShift_bvar (L := $L) (μ := ℕ) (n := $n) $x)
    return ⟨q(#$z), e⟩
  | ~q(&$x)                                       => return ⟨q(&$x), q(SubTerm.bShift_fvar $x)⟩
  | ~q(func (arity := $arity) $f $v)              => do
    let ⟨v', ve'⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L ($n + 1)))
      q(@bShift $L ℕ $n) resultBShift arity v
    return ⟨q(func $f $v'), q(bShift_func_of_eq $f $ve')⟩
  | ~q(substs (n := $k) $w $t)                    => do
    let ⟨w', we⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L ($n + 1)))
      q(@SubTerm.bShift $L ℕ $n) resultBShift k w
    let ⟨t', te⟩ ← resultSubsts w' t
    return ⟨t', q(bShift_substs_of_eq $we $te)⟩
  | ~q(SubTerm.Operator.const $c)                 => return ⟨q(SubTerm.Operator.const $c), q(bShift_const $c)⟩
  | ~q(Operator.operator (ι := Fin $arity) $f $v) => do
    let ⟨v', ve'⟩ ← resultVectorOfResultFun (u := u) (v := u)
      (α := q(SyntacticSubTerm $L $n)) (β := q(SyntacticSubTerm $L ($n + 1)))
      q(@bShift $L ℕ $n) resultBShift arity v
    return ⟨q(Operator.operator $f $v'), q(bShift_finitary_of_eq $f $ve')⟩
  | ~q($t)                                        => do
    return ⟨q(bShift $t), q(rfl)⟩

inductive NumeralUnfoldOption
  | none
  | unfoldSucc
  | all

partial def natLitResult {L : Q(Language.{u})}
  (iz : Q(Language.Zero $L)) (io : Q(Language.One $L)) (ia : Q(Language.Add $L)) (n : Q(ℕ)) :
    NumeralUnfoldOption → (z : Q(ℕ)) → MetaM $ (res : Q(SyntacticSubTerm $L $n)) × Q(natLit $L $z = $res)
  | NumeralUnfoldOption.none       =>
    fun z => do
    return ⟨q(natLit $L $z), q(rfl)⟩
  | NumeralUnfoldOption.unfoldSucc =>
    fun z =>
      match z with
      | ~q(0)      => return ⟨q(natLit $L 0), q(rfl)⟩
      | ~q(1)      => return ⟨q(natLit $L 1), q(rfl)⟩
      | ~q(.succ $ .succ $z)       => do
        let z' ← natAppFunQ Nat.succ z
        let e := q(@rfl _ (@Operator.const $L ℕ $n (natLit $L (.succ (.succ $z)))))
        return ⟨q(func Language.Add.add ![natLit $L $z', natLit $L 1]), e⟩
      | ~q($z)      => return ⟨q(natLit $L $z), q(rfl)⟩
  | NumeralUnfoldOption.all        =>
    fun z =>
      match z with
      | ~q(0)      => return ⟨q(natLit $L 0), q(rfl)⟩
      | ~q(1)      => return ⟨q(natLit $L 1), q(rfl)⟩
      | ~q(.succ $ .succ $z) => do
        let ⟨e, he⟩ ← natLitResult iz io ia n NumeralUnfoldOption.all q(.succ $z)
        return ⟨q(func Language.Add.add ![$e, natLit $L 1]), q(natLit_succ_of_eq $e $he)⟩
      | ~q($z)      => return ⟨q(natLit $L $z), q(rfl)⟩

partial def result (tp : NumeralUnfoldOption) {L : Q(Language.{u})} {n : Q(ℕ)} : (t : Q(SyntacticSubTerm $L $n)) →
    MetaM ((res : Q(SyntacticSubTerm $L $n)) × Q($t = $res))
  | ~q(#$x)                                       => pure ⟨q(#$x), q(rfl)⟩
  | ~q(&$x)                                       => pure ⟨q(&$x), q(rfl)⟩
  | ~q(func (arity := $arity) $f $v)              => do
    let ⟨vn, ve⟩ ← resultVectorOfResult (α := q(SyntacticSubTerm $L $n)) (u := u) (result tp) arity v
    return ⟨q(func $f $vn), q(func_congr $f $ve)⟩
  | ~q(free $t)                                   => do
    let ⟨tn, e⟩ ← result tp (L := L) (n := q(.succ $n)) t
    let ⟨tnn, ee⟩ ← resultFree (L := L) (n := n) tn
    return ⟨q($tnn), q(free_congr_eq $e $ee)⟩
  | ~q(substs (n := $k) $w $t)                    => do
    let ⟨t', te⟩ ← result tp (L := L) (n := k) t
    let ⟨w', we⟩ ← resultVectorOfResult (α := q(SyntacticSubTerm $L $n)) (u := u) (result tp) k w
    let ⟨e, t''⟩ ← resultSubsts (u := u) w' t'
    return ⟨e, q(substs_eq_of_eq $we $te $t'')⟩
  | ~q(shift $t)                                  => do
    let ⟨t', te⟩ ← result tp (L := L) (n := q($n)) t
    let ⟨t'', tee⟩ ← resultShift (L := L) (n := n) t'
    return ⟨q($t''), q(shift_congr_eq $te $tee)⟩
  | ~q(SubTerm.Operator.const $ natLit (hz := $hz) (ho := $ho) (ha := $ha) $z) => natLitResult hz ho ha n tp z
  | ~q(Operator.operator (ι := Fin $arity) $f $v) => do
    let ⟨vn, ve⟩ ← resultVectorOfResult (α := q(SyntacticSubTerm $L $n)) (u := u) (result tp) arity v
    return ⟨q(Operator.operator $f $vn), q(finitary_congr $f $ve)⟩
  | ~q($t)                                        => pure ⟨q($t), q(rfl)⟩

elab "dbg" : tactic => do
  let goalType ← Elab.Tactic.getMainTarget
  let some ⟨.succ u, ty⟩ ← checkSortQ' goalType | throwError "error: not a type"
  let ~q(DbgResult (SyntacticSubTerm $L $n) $t) := ty | throwError "error: not a type"
  logInfo m!"t = {t}"
  let t : Q(SyntacticSubTerm $L $n) ← withReducible <| whnf t
  let ⟨tn, e⟩ ← result NumeralUnfoldOption.none (L := L) (n := n) t
  let ⟨tnbs, ebs⟩ ← resultBShift (L := L) (n := n) tn
  logInfo m!"tn = {tn}"
  logInfo m!"tnbs = {tnbs}"
  --logInfo m!"e = {e}"
  let c : Q(DbgResult (SyntacticSubTerm $L $n) $t) := (q(DbgResult.intro ($t) $tn $e) : Expr)
  Lean.Elab.Tactic.closeMainGoal c

example {t : SyntacticSubTerm Language.oring 2} : DbgResult (SyntacticSubTerm Language.oring 12)
    (shift $ substs ![substs ![ᵀ“6”, ᵀ“&7”] t, ᵀ“3 + &6”] ᵀ“(ᵀ!t) + (#0 * ᵀ!(shift ᵀ“#1 + 9 * #1”)) + &7”) :=
  by dbg

example (t : SyntacticSubTerm Language.oring 3) : DbgResult (SyntacticSubTerm Language.oring 12)
    $ free $ ᵀ“((#0 + #1 + #2 + 8 * ᵀ!t) ᵀ⟦#2, 7, 4⟧ ᵀ⟦4, 4, 5⟧) * 8” :=
  by dbg

example : 1 ≠ 2 := of_decide_eq_true rfl

end Meta

end SubTerm
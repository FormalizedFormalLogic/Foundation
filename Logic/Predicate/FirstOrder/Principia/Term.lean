import Logic.Predicate.FirstOrder.Basic.Term.Elab
import Logic.Vorspiel.Meta
open Qq Lean Elab Meta Tactic

-- Subterm normalization

namespace LO

namespace FirstOrder

namespace Principia

namespace lemmataTerm

variable {L : Language.{u}} {μ : Type v} {n}

section term
open Subterm

lemma func_ext {k} (f : L.func k) (v w : Fin k → Subterm L μ₁ n₁) (H : ∀ i, v i = w i) :
    func f v = func f w := congr_arg _ (funext H)

lemma operator_ext {k} (f : Finitary L k) (v w : Fin k → Subterm L μ n) (H : ∀ i, v i = w i) :
    f.operator v = f.operator w := congr_arg _ (funext H)

lemma substs_ext {k} {t u : Subterm L μ k} {v w : Fin k → Subterm L μ n} (ht : t = u) (H : ∀ i, v i = w i) :
    Rew.substs v t = Rew.substs w u := congr_arg₂ _ (congr_arg _ (funext H)) ht

lemma substs_bvar_eq_of_eq {n n'} {w : Fin n → Subterm L μ n'} {x : Fin n} {t} (h : w x = t) :
    Rew.substs w #x = t :=
  by simp[h]

section Rew

variable (ω : Rew L μ₁ n₁ μ₂ n₂)

lemma rew_func_eq_of_eq {k} (f : L.func k) {v : Fin k → Subterm L μ₁ n₁} {v'} (h : ∀ i, ω (v i) = v' i) :
    ω (func f v) = func f v' :=
  by simp[Rew.func, Function.comp, h]

lemma rew_finitary_eq_of_eq {k} (f : Finitary L k) {v : Fin k → Subterm L μ₁ n₁} {v'} (h : ∀ i, ω (v i) = v' i) :
    ω (f.operator v) = f.operator v' :=
  by simp[Rew.operator, Function.comp, h]

lemma rew_const_eq_of_eq (c : Const L) :
    ω (Operator.const c) = Operator.const c :=
  by simp

end Rew

lemma shift_substs_eq_of_eq {t : SyntacticSubterm L k} {w : Fin k → SyntacticSubterm L n} {t' w'}
  (ht : Rew.shift t = t') (hw : ∀ i, Rew.shift (w i) = w' i) :
    Rew.shift (Rew.substs w t) = Rew.substs w' t' := by
  simp[←ht, ←hw, ←Rew.comp_app, Rew.shift_comp_substs]
  congr; funext i; simp[hw]

end term

end lemmataTerm

inductive DTerm (L : Q(Language.{u})) : ℕ → Type
  | bvar {n} : Fin n → DTerm L n
  | fvar {n} : ℕ → DTerm L n
  | func {n arity : ℕ} : Q(($L).func $arity) → (Fin arity → DTerm L n) → DTerm L n
  | operator {n arity : ℕ} (f : Q(Subterm.Finitary.{u, 0} $L $arity)) : (Fin arity → DTerm L n) → DTerm L n
  | const {n} (c : Q(Subterm.Const.{u, 0} $L)) : DTerm L n
  | substs : ∀ {arity}, (Fin arity → DTerm L n) → DTerm L arity → DTerm L n
  | shift {n} : DTerm L n → DTerm L n
  | bShift {n} : DTerm L n → DTerm L (n + 1)
  | fix {n} : DTerm L n → DTerm L (n + 1)
  | free {n} : DTerm L (n + 1) → DTerm L n
  | raw {n : ℕ} : Q(SyntacticSubterm $L $n) → DTerm L n

mutual

partial def toDTermZero (L : Q(Language.{u})) (n : ℕ) : (t : Q(SyntacticSubterm $L $n)) → MetaM (DTerm L n)
  | ~q(#$x) => do
    let some x' := ←@Qq.finQVal q($n) (←whnf x) | throwError m! "error in toDTerm₁: {x}"
    let some x'' := n.toFin x' | throwError m! "error in toDTerm₂: {x'}"
    return DTerm.bvar x''
  | ~q(&$x) => do
    let some x' := Lean.Expr.natLit? (←whnf x) | throwError "error in toDTerm₂: {x}"
    return DTerm.fvar x'
  | ~q(Subterm.func (arity := $arity) $f $v) => do
    let some arity' := Lean.Expr.natLit? (←whnf arity) | throwError "error in toDTerm₃: {arity}"
    let v' ← vecUnfold q(SyntacticSubterm $L $n) arity' v
    let v'' ← Matrix.getM fun i => toDTerm L n (v' i)
    return DTerm.func f v''
  | ~q(Subterm.Operator.operator (ι := Fin $arity) $o $v) => do
    let some arity' := Lean.Expr.natLit? (←whnf arity) | throwError "error in toDTerm₃: {arity}"
    let v' ← vecUnfold q(SyntacticSubterm $L $n) arity' v
    let v'' ← Matrix.getM fun i => toDTerm L n (v' i)
    return DTerm.operator o v''
  | ~q(Subterm.Operator.const $c) => return DTerm.const c
  | ~q(Rew.substs (n := $arity) $v $t) => do
    let some arity' := Lean.Expr.natLit? (←whnf arity) | throwError "error in toDTerm₃: {arity}"
    let v' ← vecUnfold q(SyntacticSubterm $L $n) arity' v
    let v'' ← Matrix.getM fun i => toDTerm L n (v' i)
    let t' ← toDTerm L arity' t
    return DTerm.substs v'' t'
  | ~q(Rew.shift $t) => return DTerm.shift (←toDTerm L n t)
  | ~q(Rew.free $t)  => return DTerm.free (←toDTerm L (n + 1) t)
  | ~q($t) => do
    logInfo m! "nonexhaustive match in toDTerm: {t}"
    return DTerm.raw t

partial def toDTerm (L : Q(Language.{u})) : (n : ℕ) → (t : Q(SyntacticSubterm $L $n)) → MetaM (DTerm L n)
  | 0,     t => toDTermZero L 0 t
  | n + 1, t =>
    match t with
    | ~q(Rew.bShift $t') => return DTerm.bShift (←toDTerm L n t')
    | ~q(Rew.fix $t')    => return DTerm.fix (←toDTerm L n t')
    | ~q($t')            => toDTermZero L (n + 1) t

end

@[reducible] partial def DTerm.toExpr {L : Q(Language.{u})} {n : ℕ} :
    DTerm L n → Q(SyntacticSubterm $L $n)
  | bvar x       => q(#$x)
  | fvar x       => q(&$x)
  | func f v     =>
    let w := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
    q(Subterm.func $f $w)
  | operator o v =>
    let w := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
    q(Subterm.Operator.operator $o $w)
  | const c      => q(Subterm.Operator.const $c)
  | substs v t   =>
    let w := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
    q(Rew.substs $w $t.toExpr)
  | shift t      => q(Rew.shift $t.toExpr)
  | bShift t     => q(Rew.bShift $t.toExpr)
  | fix t        => q(Rew.fix $t.toExpr)
  | free t       => q(Rew.free $t.toExpr)
  | raw e        => e

namespace DTerm

structure DEq {L : Q(Language.{u})} {n : ℕ} (t₁ t₂ : DTerm L n) where
  expr : Q($(t₁.toExpr) = $(t₂.toExpr))

namespace DEq

variable {L : Q(Language.{u})} {n : ℕ}

local infix:20 " ≡ " => DTerm.DEq

instance (t₁ t₂ : DTerm L n) : Inhabited (t₁ ≡ t₂) := ⟨⟨default⟩⟩

@[refl] protected def refl (t : DTerm L n) : t ≡ t := .mk q(rfl)

@[symm] protected def symm {t₁ t₂ : DTerm L n} (h : t₁ ≡ t₂) : t₂ ≡ t₁ :=
  .mk q(Eq.symm $h.expr)

@[trans] protected def trans {t₁ t₂ t₃ : DTerm L n} (h₁ : t₁ ≡ t₂) (h₂ : t₂ ≡ t₃) : t₁ ≡ t₃ :=
  .mk q(Eq.trans $h₁.expr $h₂.expr)

def funcExt {arity : ℕ} (f : Q(($L).func $arity)) {v w : Fin arity → DTerm L n} (H : (i : Fin arity) → v i ≡ w i) :
    func f v ≡ func f w := by
  let v' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
  let w' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (w i).toExpr)
  let H : Q(∀ i, $v' i = $w' i) := vecFoldDep q(fun i => $v' i = $w' i) (fun i => (H i).expr)
  let e : Q(Subterm.func $f $v' = Subterm.func $f $w') := q(lemmataTerm.func_ext $f _ _ $H)
  exact .mk e

def operatorExt {arity : ℕ}
  (f : Q(Subterm.Finitary.{u, 0} $L $arity)) {v w : Fin arity → DTerm L n} (H : (i : Fin arity) → v i ≡ w i) :
    operator f v ≡ operator f w := by
  let v' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
  let w' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (w i).toExpr)
  let H : Q(∀ i, $v' i = $w' i) := vecFoldDep q(fun i => $v' i = $w' i) (fun i => (H i).expr)
  let e : Q(($f).operator $v' = ($f).operator $w') := q(lemmataTerm.operator_ext $f _ _ $H)
  exact .mk e

def substsExt {arity : ℕ} {t₁ t₂ : DTerm L arity} {v₁ v₂ : Fin arity → DTerm L n}
  (Ht : t₁ ≡ t₂) (H : (i : Fin arity) → v₁ i ≡ v₂ i) :
    substs v₁ t₁ ≡ substs v₂ t₂ := by
  let t₁' := t₁.toExpr
  let t₂' := t₂.toExpr    
  let v₁' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v₁ i).toExpr)
  let v₂' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v₂ i).toExpr)
  let Ht : Q($t₁' = $t₂') := Ht.expr
  let H : Q(∀ i, $v₁' i = $v₂' i) := vecFoldDep q(fun i => $v₁' i = $v₂' i) (fun i => (H i).expr)
  let e : Q(Rew.substs $v₁' $t₁' = Rew.substs $v₂' $t₂') := q(lemmataTerm.substs_ext $Ht $H)
  exact .mk e

def shiftExt {t₁ t₂ : DTerm L n} (H : t₁ ≡ t₂) :
    shift t₁ ≡ shift t₂ := by
  let t₁' := t₁.toExpr
  let t₂' := t₂.toExpr
  let H : Q($t₁' = $t₂') := H.expr
  let h : Q(Rew.shift $t₁' = Rew.shift $t₂') := q(congr_arg _ $H)
  exact .mk h

def substsBvar {arity : ℕ} (x : Fin arity) (v : Fin arity → DTerm L n) : ((bvar x).substs v : DTerm L n) ≡ v x :=
  let v' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
  let t := (v x).toExpr
  let ht : Q($v' $x = $t) := (q(@rfl (SyntacticSubterm $L $n) $t) : Expr)
  let e : Q(Rew.substs $v' #$x = $t) := q(lemmataTerm.substs_bvar_eq_of_eq $ht)
  .mk e

/-
def substsBvar {arity : ℕ} (x : Fin arity) (v : Fin arity → DTerm L n) : MetaM (((bvar x).substs v : DTerm L n) ≡ v x) := do
  let v' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
  let ⟨t, ht⟩ ← vectorGet v' x
  let e : Q(Rew.substs $v' #$x = $t) := q(lemmataTerm.substs_bvar_eq_of_eq $ht)
  return .mk e
-/

def substsFvar {arity : ℕ} (v : Fin arity → DTerm L n) (x : ℕ) : ((fvar x).substs v : DTerm L n) ≡ fvar x :=
  let v' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
  let e : Q((Rew.substs $v' &$x : SyntacticSubterm $L $n) = &$x) := q(Rew.substs_fvar _ $x)
  .mk e

def substsFunc {arity k : ℕ} {z : Fin k → DTerm L n} (f : Q(($L).func $arity))
  {v : Fin arity → DTerm L k} {w : Fin arity → DTerm L n}
  (H : ∀ i, (v i).substs z ≡ w i) : (func f v).substs z ≡ func f w := by
  let z' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (z i).toExpr)
  let v' := Qq.vecFold q(SyntacticSubterm $L $k) (fun i => (v i).toExpr)
  let w' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (w i).toExpr)
  let H : Q(∀ i, Rew.substs $z' ($v' i) = $w' i) := vecFoldDep q(fun i => Rew.substs $z' ($v' i) = $w' i) (fun i => (H i).expr)
  let e : Q(Rew.substs $z' (Subterm.func $f $v') = Subterm.func $f $w') := q(lemmataTerm.rew_func_eq_of_eq _ $f $H)
  exact .mk e

def shiftBvar (x : Fin n) : ((bvar x).shift : DTerm L n) ≡ bvar x :=
  let e : Q(Rew.shift (#$x : SyntacticSubterm $L $n) = #$x) := q(Rew.shift_bvar $x)
  .mk e

def shiftFvar (x : ℕ) : ((fvar x).shift : DTerm L n) ≡ fvar (x + 1) :=
  let e : Q(Rew.shift (&$x : SyntacticSubterm $L $n) = &($x + 1)) := q(Rew.shift_fvar $x)
  .mk e

def shiftFunc {arity : ℕ} (f : Q(($L).func $arity)) {v w : Fin arity → DTerm L n}
  (H : ∀ i, (v i).shift ≡ w i) : (func f v).shift ≡ func f w := by
  let v' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
  let w' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (w i).toExpr)
  let H : Q(∀ i, Rew.shift ($v' i) = $w' i) := vecFoldDep q(fun i => Rew.shift ($v' i) = $w' i) (fun i => (H i).expr)
  let e : Q(Rew.shift (Subterm.func $f $v') = Subterm.func $f $w') := q(lemmataTerm.rew_func_eq_of_eq _ $f $H)
  exact .mk e

def shiftFinitary {arity : ℕ} (o : Q(Subterm.Finitary.{u, 0} $L $arity)) {v w : Fin arity → DTerm L n}
  (H : ∀ i, (v i).shift ≡ w i) : (operator o v).shift ≡ operator o w := by
  let v' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
  let w' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (w i).toExpr)
  let H : Q(∀ i, Rew.shift ($v' i) = $w' i) := vecFoldDep q(fun i => Rew.shift ($v' i) = $w' i) (fun i => (H i).expr)
  let e : Q(Rew.shift (($o).operator $v') = ($o).operator $w') := q(lemmataTerm.rew_finitary_eq_of_eq _ $o $H)
  exact .mk e

def shiftConst (c : Q(Subterm.Const.{u, 0} $L)) : ((const c).shift : DTerm L n) ≡ const c := by
  let e : Q(Rew.shift (n := $n) (Subterm.Operator.const $c) = Subterm.Operator.const $c) := q(lemmataTerm.rew_const_eq_of_eq _ $c)
  exact .mk e

def shiftSubsts {arity : ℕ} {t s : DTerm L arity} {v w : Fin arity → DTerm L n}
  (Ht : t.shift ≡ s) (H : ∀ i, (v i).shift ≡ w i) : (substs v t).shift ≡ substs w s := by
  let t' := t.toExpr
  let s' := s.toExpr
  let v' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
  let w' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (w i).toExpr)
  let Ht : Q(Rew.shift $t' = $s') := Ht.expr
  let H : Q(∀ i, Rew.shift ($v' i) = $w' i) := vecFoldDep q(fun i => Rew.shift ($v' i) = $w' i) (fun i => (H i).expr)
  let e : Q(Rew.shift (Rew.substs $v' $t') = Rew.substs $w' $s') := q(lemmataTerm.shift_substs_eq_of_eq $Ht $H)
  exact .mk e

end DEq

structure DMap (L : Q(Language.{u})) (n : ℕ) where
  toFun : DTerm L n → DTerm L n
  deq' : ∀ t : DTerm L n, t.DEq (toFun t)

variable {L : Q(Language.{u})}

def appSubstsAux (z : Fin arity → DTerm L n) : ℕ → DTerm L arity → DTerm L n
  | 0,            t            => substs z t
  | _        + 1, bvar x       => z x
  | _        + 1, fvar x       => fvar x
  | maxdepth + 1, func f v     => func f (fun i => appSubstsAux z maxdepth (v i))
  | maxdepth + 1, operator o v => operator o (fun i => appSubstsAux z maxdepth (v i))
  | _        + 1, const c      => const c
  | maxdepth + 1, t            => substs z t

def appShiftAux : ℕ → DTerm L n → DTerm L n
  | 0,            t            => shift t
  | _        + 1, bvar x       => bvar x
  | _        + 1, fvar x       => fvar (x + 1)
  | maxdepth + 1, func f v     => func f (fun i => appShiftAux maxdepth (v i))
  | maxdepth + 1, operator o v => operator o (fun i => appShiftAux maxdepth (v i))
  | _        + 1, const c      => const c

  | maxdepth + 1, substs v t   => substs (fun i => appShiftAux maxdepth (v i)) (appShiftAux maxdepth t)
  | maxdepth + 1, shift t      => appShiftAux maxdepth (appShiftAux maxdepth t)
  | _        + 1, bShift t     => shift (bShift t)
  | _        + 1, free t       => shift (free t)
  | _        + 1, fix t        => shift (fix t)
  | _        + 1, raw e        => shift (raw e)

def appShiftAuxDeq : (maxdepth : ℕ) → (t : DTerm L n) → (shift t).DEq (appShiftAux maxdepth t)
  | 0,            t            => DEq.refl _
  | _        + 1, bvar x       => DEq.shiftBvar x
  | _        + 1, fvar x       => DEq.shiftFvar x
  | maxdepth + 1, func f v     => DEq.shiftFunc f (fun i => appShiftAuxDeq maxdepth (v i))
  | maxdepth + 1, operator f v => DEq.shiftFinitary f (fun i => appShiftAuxDeq maxdepth (v i))
  | _        + 1, const c      => DEq.shiftConst c
  | maxdepth + 1, substs v t   => DEq.shiftSubsts (appShiftAuxDeq maxdepth t) (fun i => appShiftAuxDeq maxdepth (v i))
  | maxdepth + 1, shift t      => DEq.trans (DEq.shiftExt (appShiftAuxDeq maxdepth t)) (appShiftAuxDeq maxdepth (appShiftAux maxdepth t))
  | maxdepth + 1, bShift t     => DEq.refl _
  | maxdepth + 1, free t       => DEq.refl _
  | maxdepth + 1, fix t        => DEq.refl _
  | maxdepth + 1, raw e        => DEq.refl _

local elab "dbgappShift" : term => do
  let maxdepth := 256
  let L : Q(Language.{0}) := q(.oRing)
  let n : ℕ := 2
  let t : Q(SyntacticSubterm $L $n) := q(ᵀ“9 + #0 * &6 + #1”)
  let s : Q(SyntacticSubterm $L $n) :=
    q(Rew.shift $ Rew.substs ![Rew.substs ![ᵀ“6”, ᵀ“&7”] $t, ᵀ“3 + &6”] ᵀ“(ᵀ!$t) + (#0 * ᵀ!(Rew.fix ᵀ“#1 + 9 * #1”)) + &7”)
  let dt ← toDTerm L n s
  let e := (appShiftAux maxdepth dt).toExpr
  let eq := (appShiftAuxDeq maxdepth dt).expr
  let dbgr := q(DbgResult.intro _ _ $eq)
  logInfo m! "{s} ⟹ {e}"
  --logInfo m! "eq =def= {eq}"
  return dbgr

#eval dbgappShift

end DTerm

end Principia

end FirstOrder

end LO

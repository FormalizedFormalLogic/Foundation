import Logic.FirstOrder.Basic
import Logic.Vorspiel.Meta

open Qq Lean Elab Meta Tactic

-- Subterm normalization

namespace LO

namespace FirstOrder

namespace Principia

namespace lemmataTerm

variable {L : Language.{u}} {μ : Type v} {n}

open Subterm

lemma func_ext {k} (f : L.Func k) (v w : Fin k → Subterm L μ₁ n₁) (H : ∀ i, v i = w i) :
    func f v = func f w := congr_arg _ (funext H)

lemma Operator_ext {k} (f : Operator L k) (v w : Fin k → Subterm L μ n) (H : ∀ i, v i = w i) :
    f.operator v = f.operator w := congr_arg _ (funext H)

lemma substs_ext {k} {t u : Subterm L μ k} {v w : Fin k → Subterm L μ n} (ht : t = u) (H : ∀ i, v i = w i) :
    Rew.substs v t = Rew.substs w u := congr_arg₂ _ (congr_arg _ (funext H)) ht

lemma substs_bvar_eq_of_eq {n n'} {w : Fin n → Subterm L μ n'} {x : Fin n} {t} (h : w x = t) :
    Rew.substs w #x = t :=
  by simp[h]

section Rew

variable (ω : Rew L μ₁ n₁ μ₂ n₂)

lemma rew_func_eq_of_eq {k} (f : L.Func k) {v : Fin k → Subterm L μ₁ n₁} {v'} (h : ∀ i, ω (v i) = v' i) :
    ω (func f v) = func f v' :=
  by simp[Rew.func, Function.comp, h]

lemma rew_Operator_eq_of_eq {k} (f : Operator L k) {v : Fin k → Subterm L μ₁ n₁} {v'} (h : ∀ i, ω (v i) = v' i) :
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

lemma subst_bshift_0 (v : Fin 1 → Subterm L μ 0) (t : Subterm L μ 0) : Rew.substs v (Rew.bShift t) = t := by simp[Rew.comp]

end lemmataTerm

inductive DTerm (L : Q(Language.{u})) : ℕ → Type
  | bvar {n} : Fin n → DTerm L n
  | fvar {n} : ℕ → DTerm L n
  | func {n arity : ℕ} : Q(($L).func $arity) → (Fin arity → DTerm L n) → DTerm L n
  | Operator {n arity : ℕ} (f : Q(Subterm.Operator $L $arity)) : (Fin arity → DTerm L n) → DTerm L n
  | const {n} (c : Q(Subterm.Const $L)) : DTerm L n
  | expr {n : ℕ} : Q(SyntacticSubterm $L $n) → DTerm L n

namespace DTerm

instance : Inhabited (DTerm L n) := ⟨fvar 0⟩

def toStr {L : Q(Language.{u})} {n : ℕ} : DTerm L n → String
  | bvar x       => "#" ++ toString x
  | fvar x       => "&" ++ toString x
  | func _ v     => "func" ++ " " ++ "(" ++ (String.vecToStr fun i => (v i).toStr) ++ ")"
  | Operator _ v => "f" ++ " " ++ "(" ++ (String.vecToStr fun i => (v i).toStr) ++ ")"
  | const _      => "const"
  | expr _       => "expr"

instance : Repr (DTerm L n) := ⟨fun t _ => DTerm.toStr t⟩

instance : ToString (DTerm L n) := ⟨DTerm.toStr⟩

@[reducible] def toExpr {L : Q(Language.{u})} {n : ℕ} :
    DTerm L n → Q(SyntacticSubterm $L $n)
  | bvar x       => q(#$x)
  | fvar x       => q(&$x)
  | func f v     =>
    let w := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
    q(Subterm.func $f $w)
  | Operator o v =>
    let w := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
    q(Subterm.Operator.operator $o $w)
  | const c      => q(Subterm.Operator.const $c)
  | expr e        => e

protected def isDefEq {L : Q(Language.{u})} {n} (t₁ t₂ : DTerm L n) : MetaM Bool :=
  Lean.Meta.isDefEq t₁.toExpr t₂.toExpr

partial def denote (L : Q(Language.{u})) (n : ℕ) : (t : Q(SyntacticSubterm $L $n)) → MetaM (DTerm L n)
  | ~q(#$x) => do
    let x' : Fin n ← Denotation.denote x
    return DTerm.bvar x'
  | ~q(&$x) => do
    let x' : ℕ ← Denotation.denote x
    return DTerm.fvar x'
  | ~q(Subterm.func (arity := $arity) $f $v) => do
    let arity' : ℕ ← Denotation.denote arity
    let v' ← vecUnfold q(SyntacticSubterm $L $n) arity' v
    let v'' ← Matrix.getM fun i => denote L n (v' i)
    return DTerm.func f v''
  | ~q(Subterm.Operator.operator (arity := $arity) $o $v) => do
    let arity' : ℕ ← Denotation.denote arity
    let v' ← vecUnfold q(SyntacticSubterm $L $n) arity' v
    let v'' ← Matrix.getM fun i => denote L n (v' i)
    return DTerm.Operator o v''
  | ~q(Subterm.Operator.const $c) => return DTerm.const c
  | ~q($t) => do
    logInfo m! "nonexhaustive match in denote: {t}"
    return DTerm.expr t

instance (L : Q(Language.{u})) (n) : Denotation (DTerm L n) where
  denote := denote L n
  toExpr := toExpr

structure DEq {L : Q(Language.{u})} {n : ℕ} (t₁ t₂ : DTerm L n) where
  expr : Q($(t₁.toExpr) = $(t₂.toExpr))

local infix:20 " ≡ " => DTerm.DEq

namespace DEq

variable {L : Q(Language.{u})} {n : ℕ}

@[refl] protected def refl (t : DTerm L n) : t ≡ t := .mk q(rfl)

@[symm] protected def symm {t₁ t₂ : DTerm L n} (h : t₁ ≡ t₂) : t₂ ≡ t₁ :=
  .mk q(Eq.symm $h.expr)

@[trans] protected def trans {t₁ t₂ t₃ : DTerm L n} (h₁ : t₁ ≡ t₂) (h₂ : t₂ ≡ t₃) : t₁ ≡ t₃ :=
  .mk q(Eq.trans $h₁.expr $h₂.expr)

def ofIsDefEq (t₁ t₂ : DTerm L n) : t₁ ≡ t₂ := ⟨(q(@rfl (SyntacticSubterm $L $n) $t₁.toExpr) : Expr)⟩

def funcExt {arity : ℕ} (f : Q(($L).func $arity)) {v w : Fin arity → DTerm L n} (H : (i : Fin arity) → v i ≡ w i) :
    func f v ≡ func f w := by
  let v' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
  let w' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (w i).toExpr)
  let H : Q(∀ i, $v' i = $w' i) := vecFoldDep q(fun i => $v' i = $w' i) (fun i => (H i).expr)
  let e : Q(Subterm.func $f $v' = Subterm.func $f $w') := q(lemmataTerm.func_ext $f _ _ $H)
  exact .mk e

def OperatorExt {arity : ℕ}
  (f : Q(Subterm.Operator $L $arity)) {v w : Fin arity → DTerm L n} (H : (i : Fin arity) → v i ≡ w i) :
    Operator f v ≡ Operator f w := by
  let v' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
  let w' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (w i).toExpr)
  let H : Q(∀ i, $v' i = $w' i) := vecFoldDep q(fun i => $v' i = $w' i) (fun i => (H i).expr)
  let e : Q(($f).operator $v' = ($f).operator $w') := q(lemmataTerm.Operator_ext $f _ _ $H)
  exact .mk e

/-
section Numeral

variable (iz : Q(Language.Zero $L)) (io : Q(Language.One $L)) (ia : Q(Language.Add $L))

def numeralEq : (z : ℕ) → (t : DTerm L n) × (const q(Subterm.numeral $L $z) ≡ t)
  | 0 => ⟨const q(Subterm.numeral $L 0), DEq.refl _⟩
  | 1 => ⟨const q(Subterm.numeral $L 1), DEq.refl _⟩
  | z + 2 => ⟨  (numeralEq (z + 1)).1, by {  }⟩

def unfoldNumeral : (t : DTerm L n) → MetaM ((t' : DTerm L n) × (t ≡ t'))
  | bvar x       => pure ⟨bvar x, DEq.refl _⟩
  | fvar x       => pure ⟨fvar x, DEq.refl _⟩
  | func f v     => do
    let w ← Matrix.getM fun i => unfoldNumeral (v i)
    return ⟨func f (fun i => (w i).1), funcExt f fun i => (w i).2⟩
  | Operator f v => do
    let w ← Matrix.getM fun i => unfoldNumeral (v i)
    return ⟨Operator f (fun i => (w i).1), OperatorExt f fun i => (w i).2⟩
  | const c      =>
    match c with
    |
  | DTerm.expr e => pure ⟨DTerm.expr e, DEq.refl _⟩

end Numeral
-/

end DEq

abbrev qrew (L : Q(Language.{u})) (n m: ℕ) (ω : Q(Rew $L ℕ $n ℕ $m)) : Q(SyntacticSubterm $L $n → SyntacticSubterm $L $m) := q($ω)

abbrev qsubsts {L : Q(Language.{u})} {arity n : ℕ} (v : Fin arity → DTerm L n) :
    Q(SyntacticSubterm $L $arity → SyntacticSubterm $L $n) :=
  let v' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
  qrew L arity n q(Rew.substs $v')

abbrev qshift {L : Q(Language.{u})} {n : ℕ} : Q(SyntacticSubterm $L $n → SyntacticSubterm $L $n) :=
  qrew L n n q(Rew.shift)

abbrev qbShift {L : Q(Language.{u})} {n : ℕ} : Q(SyntacticSubterm $L $n → SyntacticSubterm $L ($n + 1)) :=
  qrew L n (n + 1) q(Rew.bShift)

abbrev qfix {L : Q(Language.{u})} {n : ℕ} : Q(SyntacticSubterm $L $n → SyntacticSubterm $L ($n + 1)) :=
  qrew L n (n + 1) q(Rew.fix)

abbrev qfree {L : Q(Language.{u})} {n : ℕ} : Q(SyntacticSubterm $L ($n + 1) → SyntacticSubterm $L $n) :=
  qrew L (n + 1) n q(Rew.free)

structure DEqFun {L : Q(Language.{u})} {n₁ n₂ : ℕ} (f : Q(SyntacticSubterm $L $n₁ → SyntacticSubterm $L $n₂))
  (t₁ : DTerm L n₁) (t₂ : DTerm L n₂) where
  expr : Q($f $(t₁.toExpr) = $(t₂.toExpr))

local notation:25 t₁ " ≡[" f:25 "] " t₂:0 => DTerm.DEqFun f t₁ t₂

namespace DEqFun

variable {L : Q(Language.{u})} {n : ℕ}

def ofDEqFunOfDEq {n₁ n₂ : ℕ} {f : Q(SyntacticSubterm $L $n₁ → SyntacticSubterm $L $n₂)}
  {t₁ : DTerm L n₁} {t₂ t₂' : DTerm L n₂} (df : t₁ ≡[f] t₂) (de : t₂ ≡ t₂') :
    t₁ ≡[f] t₂' := ⟨q(Eq.trans $df.expr $de.expr)⟩

def rewFunc {arity n m : ℕ} (ω : Q(Rew $L ℕ $n ℕ $m)) (f : Q(($L).func $arity))
  {v : Fin arity → DTerm L n} {w : Fin arity → DTerm L m}
  (H : ∀ i, v i ≡[qrew L n m ω] w i) : func f v ≡[qrew L n m ω] func f w := by
  let v' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
  let w' := Qq.vecFold q(SyntacticSubterm $L $m) (fun i => (w i).toExpr)
  let H : Q(∀ i, $ω ($v' i) = $w' i) := vecFoldDep q(fun i => $ω ($v' i) = $w' i) (fun i => (H i).expr)
  let e : Q($ω (Subterm.func $f $v') = Subterm.func $f $w') := q(lemmataTerm.rew_func_eq_of_eq _ $f $H)
  exact .mk e

def rewOperator {arity n m : ℕ} (ω : Q(Rew $L ℕ $n ℕ $m))
  (o : Q(Subterm.Operator $L $arity)) {v : Fin arity → DTerm L n} {w : Fin arity → DTerm L m}
  (H : ∀ i, v i ≡[qrew L n m ω] w i) : Operator o v ≡[qrew L n m ω] Operator o w := by
  let v' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
  let w' := Qq.vecFold q(SyntacticSubterm $L $m) (fun i => (w i).toExpr)
  let H : Q(∀ i, $ω ($v' i) = $w' i) := vecFoldDep q(fun i => $ω ($v' i) = $w' i) (fun i => (H i).expr)
  let e : Q($ω (($o).operator $v') = ($o).operator $w') := q(lemmataTerm.rew_Operator_eq_of_eq _ $o $H)
  exact .mk e

def rewConst {n m : ℕ} (ω : Q(Rew $L ℕ $n ℕ $m))
  (c : Q(Subterm.Const $L)) : (const c : DTerm L n) ≡[qrew L n m ω] const c := by
  let e : Q($ω (Subterm.Operator.const $c) = Subterm.Operator.const $c) := q(lemmataTerm.rew_const_eq_of_eq _ $c)
  exact .mk e

def substsBvar {arity : ℕ} (v : Fin arity → DTerm L n) (x : Fin arity)  :
    (bvar x : DTerm L arity) ≡[qsubsts v] v x :=
  let v' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
  let t := (v x).toExpr
  let ht : Q($v' $x = $t) := (q(@rfl (SyntacticSubterm $L $n) $t) : Expr)
  let e : Q(Rew.substs $v' #$x = $t) := q(lemmataTerm.substs_bvar_eq_of_eq $ht)
  .mk e

def substsFvar {arity : ℕ} (v : Fin arity → DTerm L n) (x : ℕ) : (fvar x : DTerm L arity) ≡[qsubsts v] fvar x :=
  let v' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
  let e : Q((Rew.substs $v' &$x : SyntacticSubterm $L $n) = &$x) := q(Rew.substs_fvar _ $x)
  .mk e

def shiftBvar (x : Fin n) : (bvar x : DTerm L n) ≡[qshift] bvar x :=
  let e : Q(Rew.shift (#$x : SyntacticSubterm $L $n) = #$x) := q(Rew.shift_bvar $x)
  .mk e

def shiftFvar (x : ℕ) : (fvar x : DTerm L n) ≡[qshift] fvar (x + 1) :=
  let e : Q(Rew.shift (&$x : SyntacticSubterm $L $n) = &($x + 1)) := q(Rew.shift_fvar $x)
  .mk e

def bShiftBvar (x : Fin n) : (bvar x : DTerm L n) ≡[@qbShift _ L n] bvar x.succ :=
  let e : Q(Rew.bShift (#$x : SyntacticSubterm $L $n) = #($x).succ) := q(Rew.bShift_bvar $x)
  .mk e

def bShiftFvar (x : ℕ) : (fvar x : DTerm L n) ≡[@qbShift _ L n] (fvar x : DTerm L (n + 1)) :=
  let e : Q(Rew.bShift (&$x : SyntacticSubterm $L $n) = &$x) := q(Rew.bShift_fvar $x)
  .mk e

def freeBvar (x : Fin (n + 1)) : (bvar x : DTerm L (n + 1)) ≡[@qfree _ L n] x.lastCases (fvar 0) bvar :=
  x.lastCases
    ( let e : Q(Rew.free (#(Fin.last $n) : SyntacticSubterm $L ($n + 1)) = &0) := q(Rew.free_bvar_last)
      .mk e)
    ( fun x' : Fin n =>
      let e : Q(Rew.free (#(Fin.castSucc $x') : SyntacticSubterm $L ($n + 1)) = #$x') := q(Rew.free_bvar_castSucc $x')
      .mk e)

def freeFvar (x : ℕ) : (fvar x : DTerm L (n + 1)) ≡[@qfree _ L n] (fvar (x + 1) : DTerm L n) :=
  let e : Q(Rew.free (&$x : SyntacticSubterm $L ($n + 1)) = &($x + 1)) := q(Rew.free_fvar $x)
  .mk e

def fixBvar (x : Fin n) : (bvar x : DTerm L n) ≡[@qfix _ L n] bvar x.castSucc :=
  let e : Q(Rew.fix (#$x : SyntacticSubterm $L $n) = #($x).castSucc) := q(Rew.fix_bvar $x)
  .mk e

def fixFvar (x : ℕ) : (fvar x : DTerm L n) ≡[@qfix _ L n] x.casesOn (bvar (Fin.last n)) fvar :=
  x.casesOn
    ( let e : Q(Rew.fix (&0 : SyntacticSubterm $L $n) = #(Fin.last $n)) := q(Rew.fix_fvar_zero)
      .mk e)
    ( fun x' : ℕ =>
      let e : Q(Rew.fix (&($x' + 1) : SyntacticSubterm $L $n) = &$x') := q(Rew.fix_fvar_succ $x')
      .mk e)

end DEqFun

structure DEqFunMap (L : Q(Language.{u})) (n₁ n₂ : ℕ) (f : Q(SyntacticSubterm $L $n₁ → SyntacticSubterm $L $n₂)) where
  toFun : (t₁ : DTerm L n₁) → (t₂ : DTerm L n₂) × (t₁ ≡[f] t₂)

namespace DEqFunMap

variable {L : Q(Language.{u})}

instance (n₁ n₂ : ℕ) (f : Q(SyntacticSubterm $L $n₁ → SyntacticSubterm $L $n₂)) :
    CoeFun (DEqFunMap L n₁ n₂ f) (fun _ => DTerm L n₁ → DTerm L n₂) := ⟨fun d t => (d.toFun t).1⟩

def deq {n₁ n₂ : ℕ} {f : Q(SyntacticSubterm $L $n₁ → SyntacticSubterm $L $n₂)} (d : DEqFunMap L n₁ n₂ f) (t : DTerm L n₁) :
    t ≡[f] d t := (d.toFun t).2

section rew

variable {m n : ℕ} (ω : Q(Rew $L ℕ $n ℕ $m))
  (bt : Fin n → DTerm L m) (ft : ℕ → DTerm L m)
  (hbt : ∀ x, bvar x ≡[qrew L n m ω] bt x) (hft : ∀ x, fvar x ≡[qrew L n m ω] ft x)

def rewAux : (t : DTerm L n) → (t' : DTerm L m) × (t ≡[qrew L n m ω] t')
  | bvar x       => ⟨bt x, hbt x⟩
  | fvar x       => ⟨ft x, hft x⟩
  | func f v     => ⟨func f (fun i => (rewAux (v i)).1), DEqFun.rewFunc _ f (fun i => (rewAux (v i)).2)⟩
  | Operator f v => ⟨Operator f (fun i => (rewAux (v i)).1), DEqFun.rewOperator _ f (fun i => (rewAux (v i)).2)⟩
  | const c      => ⟨const c, DEqFun.rewConst _ c⟩
  | expr e       => ⟨expr q($ω $e), .mk (q(@rfl (SyntacticSubterm $L $m) ($ω $e)) : Expr)⟩

def rew : DEqFunMap L n m (qrew L n m ω) := ⟨rewAux ω bt ft hbt hft⟩

end rew

def substs {arity n : ℕ} (z : Fin arity → DTerm L n) : DEqFunMap L arity n (qsubsts z) :=
  let z' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (z i).toExpr)
  rew q(Rew.substs $z') z fvar (DEqFun.substsBvar z) (DEqFun.substsFvar z)

def shift {n : ℕ} : DEqFunMap L n n qshift :=
  rew q(Rew.shift) bvar (fun x => fvar (x + 1)) DEqFun.shiftBvar DEqFun.shiftFvar

def bShift {n : ℕ} : DEqFunMap L n (n + 1) (@qbShift _ L n) :=
  rew q(Rew.bShift) (fun x => bvar x.succ) fvar DEqFun.bShiftBvar DEqFun.bShiftFvar

def free {n : ℕ} : DEqFunMap L (n + 1) n (@qfree _ L n) :=
  rew q(Rew.free) (fun x => x.lastCases (fvar 0) bvar) (fun x => fvar (x + 1)) DEqFun.freeBvar DEqFun.freeFvar

def fix {n : ℕ} : DEqFunMap L n (n + 1) (@qfix _ L n) :=
  rew q(Rew.fix) (fun x => bvar x.castSucc) (fun x => x.casesOn (bvar (Fin.last n)) fvar) DEqFun.fixBvar DEqFun.fixFvar

end DEqFunMap

local elab "dbgSubst" : term => do
  let L : Q(Language.{0}) := q(.oRing)
  let n : ℕ := 2
  let m : ℕ := 3
  let t : Q(SyntacticSubterm $L $n) := q(ᵀ“9 + #0 * &6 + !!(Rew.fix #1)”)
  let v : Q(Fin $n → SyntacticSubterm $L $m) := q(![ᵀ“&2 + 2”, ᵀ“#1 * 8”])
  let v' ←vecUnfold q(SyntacticSubterm $L $m) n v
  let v'' ←Matrix.getM fun i => denote L m (v' i)
  -- let s : Q(SyntacticSubterm $L $n) :=
  --   q(Rew.shift $ Rew.substs ![Rew.substs ![ᵀ“6”, ᵀ“&7”] $t, ᵀ“3 + &6”] ᵀ“(ᵀ!$t) + (#0 * ᵀ!(Rew.fix ᵀ“#1 + 9 * #1”)) + &7”)
  let dt ← denote L n t
  let fdt := DEqFunMap.substs v'' dt
  let e := fdt.toExpr
  let eq := ((DEqFunMap.substs v'').deq dt).expr
  logInfo m! "{toString dt} ⟹d {toString fdt}"
  let dbgr := q(DbgResult.intro _ _ $eq)
  logInfo m! "{t} ⟹ {e}"
  --logInfo m! "eq =def= {eq}"
  return dbgr

#eval dbgSubst

local elab "dbgFree" : term => do
  let L : Q(Language.{0}) := q(.oRing)
  let n : ℕ := 2
  let t : Q(SyntacticSubterm $L $n) := q(ᵀ“9 * (#0 + #1) + &0 * &1 + &2”)
  let dt ← denote L n t
  let fdt := DEqFunMap.free dt

  let e := fdt.toExpr
  let eq := (DEqFunMap.free.deq dt).expr
  logInfo m! "{toString dt} ⟹d {toString fdt}"
  let dbgr := q(DbgResult.intro _ _ $eq)
  logInfo m! "{t} ⟹ {e}"
  --logInfo m! "eq =def= {eq}"
  return dbgr

def findTerm (s : DTerm L 0) (t : DTerm L 0) :
  MetaM ((t' : DTerm L 1) × (t' ≡[qsubsts ![s]] t)) := do
  if ←DTerm.isDefEq s t
    then return ⟨bvar 0, DEqFun.ofDEqFunOfDEq (DEqFun.substsBvar ![s] 0) (DEq.ofIsDefEq s t)⟩
    else match t with
    | bvar x       => return Fin.elim0 x
    | fvar x       => return ⟨fvar x, DEqFun.substsFvar _ _⟩
    | func f v     =>
      let w ← Matrix.getM fun i => findTerm s (v i)
      return ⟨func f (fun i => (w i).1), DEqFun.rewFunc _ f (fun i => (w i).2)⟩
    | Operator f v =>
      let w ← Matrix.getM fun i => findTerm s (v i)
      return ⟨Operator f (fun i => (w i).1), DEqFun.rewOperator _ f (fun i => (w i).2)⟩
    | const c      => return ⟨const c, DEqFun.rewConst _ c⟩
    | expr e       => return ⟨expr q(Rew.bShift $e),
      let h : Q(Rew.substs ![$s.toExpr] (Rew.bShift $e) = $e) := q(lemmataTerm.subst_bshift_0 _ $e)
      .mk h⟩

local elab "dbgfindTerm" : term => do
  let L : Q(Language.{0}) := q(.oRing)
  let s : Q(SyntacticSubterm $L 0) := q(ᵀ“&0 + 1”)
  let t : Q(SyntacticSubterm $L 0) := q(ᵀ“9 + (&0 + 1) + 0 * (&6 + (&0 + 1) + &3 * (&0 + 1))”)
  let ds ← denote L 0 s
  let dt ← denote L 0 t
  let ⟨fdt, eq⟩ ← findTerm ds dt
  let efdt := fdt.toExpr
  let eeq := eq.expr
  logInfo m! "{toString dt} ⟹d {toString fdt}"
  let dbgr := q(DbgResult.intro _ _ $eeq)
  logInfo m! "substs ![{s}] {t} ⟹ {efdt}"
  --logInfo m! "eq =def= {eeq}"
  return dbgr

#eval dbgfindTerm

end DTerm

end Principia

end FirstOrder

end LO

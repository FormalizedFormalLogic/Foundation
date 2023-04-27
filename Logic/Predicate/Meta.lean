import Logic.Predicate.Coding
import Logic.Vorspiel.Meta
open Qq Lean Elab Meta Tactic

-- SubTerm normalization
namespace SubTerm

namespace Meta

#check Const

inductive SubTermCode.Nullary
  | numeral : Q(ℕ) → SubTermCode.Nullary
  | expr : Expr → SubTermCode.Nullary

inductive SubTermCode : Type
  | bvar : ℕ → SubTermCode
  | fvar : ℕ → SubTermCode
  | add : Expr → SubTermCode → SubTermCode → SubTermCode
  | mul : Expr → SubTermCode → SubTermCode → SubTermCode
  | num : Expr → Expr → Expr → Expr → SubTermCode  
  | func₀ : Expr → SubTermCode
  | func₁ : Expr → SubTermCode → SubTermCode
  | func₂ : Expr → SubTermCode → SubTermCode → SubTermCode
  | metavar : Expr → SubTermCode

namespace SubTermCode

def toStr : SubTermCode → String
  | bvar x   => "#" ++ toString x
  | fvar x   => "&" ++ toString x
  | func₀ _  => "const"
  | func₁ _ c => "f¹ (" ++ c.toStr
  | func₂ _ c₁ c₂ => "f² (" ++ c₁.toStr ++ ", " ++ c₂.toStr ++ ")"
  | add _ c₁ c₂   => "(" ++ c₁.toStr ++ " + " ++ c₂.toStr ++ ")"
  | mul _ c₁ c₂   => "(" ++ c₁.toStr ++ " * " ++ c₂.toStr ++ ")"
  | num _ _ _ _   => "N"
  | metavar _     => "m"

instance : Repr SubTermCode := ⟨fun b _ => b.toStr⟩

instance : ToString SubTermCode := ⟨toStr⟩

def toExpr (L : Q(Language.{u})) (n : Q(ℕ)) : SubTermCode → MetaM Q(SyntacticSubTerm $L $n)
  | bvar x         => do
    let some nval := (←whnf n).natLit? | throwError f!"Fail: natLit?: {n}"
    if x < nval then
      let lt ← decideTQ q($x < $n)
      return q(#(⟨$x, $lt⟩))
    else throwError f!"Invalid SubTermCode"
  | fvar x         => return q(&$x)
  | add e c₁ c₂    => do
    let _ : Q(Language.Add $L) := e
    let et₁ ← toExpr L n c₁
    let et₂ ← toExpr L n c₂
    return q(func Language.Add.add ![$et₁, $et₂])
  | mul e c₁ c₂    => do
    let _ : Q(Language.Mul $L) := e
    let et₁ ← toExpr L n c₁
    let et₂ ← toExpr L n c₂
    return q(func Language.Mul.mul ![$et₁, $et₂])
  | num ez eo ea e => do
    let _ : Q(Language.Zero $L) := ez
    let _ : Q(Language.One $L) := eo
    let _ : Q(Language.Add $L) := ea
    let z : Q(ℕ) := e
    return q(SubTerm.Abbrev.const (natLit $L $z))
  | func₀ e        => do
    let e : Q(($L).func 0) := e
    return q(func $e ![])
  | func₁ e c      => do
    let ef : Q(($L).func 1) := e
    let et ← toExpr L n c
    return q(func $ef ![$et])
  | func₂ e c₁ c₂  => do
    let ef : Q(($L).func 2) := e
    let et₁ ← toExpr L n c₁
    let et₂ ← toExpr L n c₂
    return q(func $ef ![$et₁, $et₂])
  | metavar e      => return e    

end SubTermCode

namespace Syntax

open Qq

partial def toSubTermCode (L : Q(Language.{u})) (n : Q(ℕ)) : Syntax → TermElabM SubTermCode
  | `(subterm| #$x)                 => do 
    let some nval := (←whnf n).natLit? | throwError f!"Fail: natLit?: {n}"
    let xval ← Lean.Syntax.isNatLit? x
    if xval < nval then
      return SubTermCode.bvar xval
    else throwError "invalid variable: {xval} ≥ {n}"
  | `(subterm| &$n)                 => do
    let nval ← Lean.Syntax.isNatLit? n
    return SubTermCode.fvar nval
  | `(subterm| const $c)            => do
    let (e : Q(($L).func 0)) ← Term.elabTerm c (return q(($L).func 0))
    return SubTermCode.func₀ e
  | `(subterm| func¹ $f/[$t])       => do
    let (e : Q(($L).func 1)) ← Term.elabTerm f (return q(($L).func 1))
    let c ← toSubTermCode L n t
    return SubTermCode.func₁ e c
  | `(subterm| func² $f/[$t₁, $t₂]) => do
    let (e : Q(($L).func 1)) ← Term.elabTerm f (return q(($L).func 1))
    let c₁ ← toSubTermCode L n t₁
    let c₂ ← toSubTermCode L n t₂
    return SubTermCode.func₂ e c₁ c₂
  | `(subterm| $t₁ + $t₂)           => do
    let c₁ ← toSubTermCode L n t₁
    let c₂ ← toSubTermCode L n t₂
    let ha : Q(Language.Add $L) ← synthInstanceQ q(Language.Add $L)
    return SubTermCode.add ha c₁ c₂
  | `(subterm| $t₁ * $t₂)           => do
    let c₁ ← toSubTermCode L n t₁
    let c₂ ← toSubTermCode L n t₂
    let hm : Q(Language.Mul $L) ← synthInstanceQ q(Language.Mul $L)
    return SubTermCode.mul hm c₁ c₂
  | `(subterm| $n:num)              => do
    let (e : Q(ℕ)) ← Term.elabTerm n (return .const `Nat [])
    let hz : Q(Language.Zero $L) ← synthInstanceQ q(Language.Zero $L)
    let ho : Q(Language.One $L) ← synthInstanceQ q(Language.One $L)
    let ha : Q(Language.Add $L) ← synthInstanceQ q(Language.Add $L)
    return SubTermCode.num hz ho ha e
  | `(subterm| ($t))                => toSubTermCode L n t
  | `(subterm| !$t)                 => do
    let (e : Q(SyntacticSubTerm $L $n)) ← Term.elabTerm t (return q(SyntacticSubTerm $L $n))
    return SubTermCode.metavar e
  | _                               => throwUnsupportedSyntax

elab "??dbg_Syntax.toSubTermCode" s:subterm  : term => do
  let el : Q(Language.{0}) := q(Language.oring)
  let en : Q(ℕ) := q(9)
  let c ← toSubTermCode el en s
  logInfo f! "{c}"
  c.toExpr el en

#eval ??dbg_Syntax.toSubTermCode (0 + #2 + 2) * &99

end Syntax

partial def toSubTermCode (L : Q(Language.{u})) : (n : Q(ℕ)) → Q(SyntacticSubTerm $L $n) → TermElabM SubTermCode
  | ~q($n), ~q(#$x) => do
    let some xval := (← finQVal (n := n) x) | throwError f!"Fail: FinQVal {x}"
    return SubTermCode.bvar xval
  | ~q($n), ~q(&$x) => do
    let some xval := (←whnf x).natLit? | throwError f!"Fail: natLit?: {x}"
    return SubTermCode.fvar xval
  | ~q($n), ~q(SubTerm.Abbrev.const (natLit (hz := $hz) (ho := $ho) (ha := $ha) $z)) => do
    return SubTermCode.num hz ho ha z
  | ~q($n), ~q(SubTerm.func (Language.Add.add (self := $ha)) ![$t, $u]) => do
    let c₁ ← toSubTermCode L n t
    let c₂ ← toSubTermCode L n u
    return SubTermCode.add ha c₁ c₂
  | ~q($n), ~q(SubTerm.func (Language.Mul.mul (self := $hm)) ![$t, $u]) => do
    let c₁ : SubTermCode ← toSubTermCode L n t
    let c₂ ← toSubTermCode L n u
    return SubTermCode.mul hm c₁ c₂
  | ~q($n), ~q(SubTerm.func $c ![])       => do
    return SubTermCode.func₀ c
  | ~q($n), ~q(SubTerm.func $f ![$t])     => do
    let c ← toSubTermCode L n t
    return SubTermCode.func₁ f c
  | ~q($n), ~q(SubTerm.func $f ![$t, $u]) => do
    let c₁ ← toSubTermCode L n t
    let c₂ ← toSubTermCode L n u
    return SubTermCode.func₂ f c₁ c₂

elab "??dbg_toSubTermCode" : term => do
  let el : Q(Language.{0}) := q(Language.oring)
  let en : Q(ℕ) := q(9)
  let c ← toSubTermCode el en q(T“(0 + #2) * 2”)
  logInfo f! "{c}"
  c.toExpr el en

#eval ??dbg_toSubTermCode

section lemmata
variable {L : Language.{u}} {μ : Type v} {n}

lemma free_bvar_last (n : ℕ) : free (#⟨n, Nat.lt.base n⟩ : SyntacticSubTerm L (n + 1)) = &0 :=
  SubTerm.free_bvar_last

lemma free_bvar_of_lt (x : Fin (n + 1)) (h : x.val < n) : free (#x : SyntacticSubTerm L (n + 1)) = #⟨x, h⟩ :=
  free_bvar_castSucc (L := L) ⟨x, h⟩

lemma free_func0 (f : L.func 0) :
    SubTerm.free (SubTerm.func (L := L) (n := n + 1) f ![]) = SubTerm.func f ![] := by simp[free_func]

lemma free_func1 (f : L.func 1) {t : SyntacticSubTerm L (n + 1)} {t'} (h : free t = t'):
    SubTerm.free (SubTerm.func f ![t]) = SubTerm.func f ![t'] := by simp[←h, free_func]; funext x; simp

lemma free_func2 (f : L.func 2) {t₁ t₂ : SyntacticSubTerm L (n + 1)} {t₁' t₂'}
  (h₁ : free t₁ = t₁') (h₂ : free t₂ = t₂') :
    SubTerm.free (SubTerm.func f ![t₁, t₂]) = SubTerm.func f ![t₁', t₂'] :=
  by simp[←h₁, ←h₂, free_func]; funext x; cases x using Fin.cases <;> simp

lemma free_func3 (f : L.func 3) {t₁ t₂ t₃ : SyntacticSubTerm L (n + 1)} {t₁' t₂' t₃'}
  (h₁ : free t₁ = t₁') (h₂ : free t₂ = t₂') (h₃ : free t₃ = t₃') :
    SubTerm.free (SubTerm.func f ![t₁, t₂, t₃]) = SubTerm.func f ![t₁', t₂', t₃'] := by
  simp[←h₁, ←h₂, ←h₃, free_func]; funext x;
  cases' x using Fin.cases with x <;> simp;
  cases' x using Fin.cases with x <;> simp

lemma subst_bvar_last (n : ℕ) (s : SubTerm L μ n) :
    subst s (#⟨n, Nat.lt.base n⟩ : SubTerm L μ (n + 1)) = s :=
  SubTerm.subst_bvar_last _

lemma subst_bvar_of_lt {s : SubTerm L μ n} (x : Fin (n + 1)) (h : x.val < n) : 
    subst s (#x : SubTerm L μ (n + 1)) = #⟨x, h⟩ :=
  subst_bvar_castSucc s ⟨x, h⟩

lemma subst_func0 {s : SubTerm L μ n} (f : L.func 0) :
    subst s (SubTerm.func (L := L) (n := n + 1) f ![]) = SubTerm.func f ![] := by simp[subst_func]

lemma subst_func1 {s : SubTerm L μ n} (f : L.func 1) {t : SubTerm L μ (n + 1)} {t'} (h : subst s t = t'):
    subst s (SubTerm.func f ![t]) = SubTerm.func f ![t'] := by simp[←h, subst_func]; funext x; simp

lemma subst_func2 {s : SubTerm L μ n} (f : L.func 2) {t₁ t₂ : SubTerm L μ (n + 1)} {t₁' t₂'}
  (h₁ : subst s t₁ = t₁') (h₂ : subst s t₂ = t₂') :
    subst s (SubTerm.func f ![t₁, t₂]) = SubTerm.func f ![t₁', t₂'] :=
  by simp[←h₁, ←h₂, subst_func]; funext x; cases x using Fin.cases <;> simp

lemma subst_func3 {s : SubTerm L μ n} (f : L.func 3) {t₁ t₂ t₃ : SubTerm L μ (n + 1)} {t₁' t₂' t₃'}
  (h₁ : subst s t₁ = t₁') (h₂ : subst s t₂ = t₂') (h₃ : subst s t₃ = t₃') :
    subst s (SubTerm.func f ![t₁, t₂, t₃]) = SubTerm.func f ![t₁', t₂', t₃'] := by
  simp[←h₁, ←h₂, ←h₃, subst_func]; funext x;
  cases' x using Fin.cases with x <;> simp;
  cases' x using Fin.cases with x <;> simp

lemma shift_func0 (f : L.func 0) :
    shift (SubTerm.func (L := L) (n := n) f ![]) = SubTerm.func f ![] := by simp

lemma shift_func1 (f : L.func 1) {t t' : SyntacticSubTerm L n} (h : shift t = t'):
    shift (SubTerm.func f ![t]) = SubTerm.func f ![t'] := by simp[←h]; funext x; simp

lemma shift_func2 (f : L.func 2) {t₁ t₂ t₁' t₂' : SyntacticSubTerm L n}
  (h₁ : shift t₁ = t₁') (h₂ : shift t₂ = t₂') :
    shift (SubTerm.func f ![t₁, t₂]) = SubTerm.func f ![t₁', t₂'] :=
  by simp[←h₁, ←h₂]; funext x; cases x using Fin.cases <;> simp

lemma shift_func3 (f : L.func 3) {t₁ t₂ t₃ t₁' t₂' t₃' : SyntacticSubTerm L n}
  (h₁ : shift t₁ = t₁') (h₂ : shift t₂ = t₂') (h₃ : shift t₃ = t₃') :
    shift (SubTerm.func f ![t₁, t₂, t₃]) = SubTerm.func f ![t₁', t₂', t₃'] := by
  simp[←h₁, ←h₂, ←h₃]; funext x;
  cases' x using Fin.cases with x <;> simp;
  cases' x using Fin.cases with x <;> simp

lemma shift_subst {t : SyntacticSubTerm L (n + 1)} {u t' u'}
  (ht : shift t = t') (hu : shift u = u') :
    shift (subst u t) = subst u' t' := by
  simp[←ht, ←hu, shift, SubTerm.subst, map, bind_bind]; congr; funext x
  cases' x using Fin.lastCases with x <;> simp

lemma bShift_func0 (f : L.func 0) :
    bShift (SubTerm.func (L := L) (μ:= μ) (n := n) f ![]) = SubTerm.func f ![] := by simp[bShift_func]

lemma bShift_func1 (f : L.func 1) {t : SubTerm L μ n} {t'} (h : bShift t = t'):
    bShift (SubTerm.func f ![t]) = SubTerm.func f ![t'] := by simp[←h, bShift_func]; funext x; simp

lemma bShift_func2 (f : L.func 2) {t₁ t₂ : SubTerm L μ n} {t₁' t₂'}
  (h₁ : bShift t₁ = t₁') (h₂ : bShift t₂ = t₂') :
    bShift (SubTerm.func f ![t₁, t₂]) = SubTerm.func f ![t₁', t₂'] :=
  by simp[←h₁, ←h₂, bShift_func]; funext x; cases x using Fin.cases <;> simp

lemma bShift_func3 (f : L.func 3) {t₁ t₂ t₃ : SyntacticSubTerm L n} {t₁' t₂' t₃'}
  (h₁ : bShift t₁ = t₁') (h₂ : bShift t₂ = t₂') (h₃ : bShift t₃ = t₃') :
    bShift (SubTerm.func f ![t₁, t₂, t₃]) = SubTerm.func f ![t₁', t₂', t₃'] := by
  simp[←h₁, ←h₂, ←h₃, bShift_func]; funext x;
  cases' x using Fin.cases with x <;> simp;
  cases' x using Fin.cases with x <;> simp

lemma bShift_subst {t : SyntacticSubTerm L (n + 1)} {u t' u'}
  (ht : bShift t = t') (hu : bShift u = u') :
    bShift (subst u t) = subst u' t' := by
  simp[←ht, ←hu, bShift, SubTerm.subst, map, bind_bind]; congr; funext x
  cases' x using Fin.lastCases with x <;> simp[Fin.succ_castSucc]

lemma func1_congr (f : L.func 1) {t t' : SyntacticSubTerm L n} (h : t = t'):
    SubTerm.func f ![t] = SubTerm.func f ![t'] := by simp[←h]

lemma func2_congr (f : L.func 2) {t₁ t₂ t₁' t₂' : SyntacticSubTerm L n}
  (h₁ : t₁ = t₁') (h₂ : t₂ = t₂') :
    SubTerm.func f ![t₁, t₂] = SubTerm.func f ![t₁', t₂'] :=
  by simp[←h₁, ←h₂]

lemma func3_congr (f : L.func 3) {t₁ t₂ t₃ t₁' t₂' t₃' : SyntacticSubTerm L n}
  (h₁ : t₁ = t₁') (h₂ : t₂ = t₂') (h₃ : t₃ = t₃') :
    SubTerm.func f ![t₁, t₂, t₃] = SubTerm.func f ![t₁', t₂', t₃'] := by
  simp[←h₁, ←h₂, ←h₃]

lemma free_congr_eq {t t' : SyntacticSubTerm L (n + 1)} {s} (e : t = t') (h : free t' = s) :
  free t = s := Eq.trans (congr_arg _ e) h

lemma subst_congr_eq {s s' : SubTerm L μ n} {t t' u} (es : s = s') (et : t = t') (h : subst s' t' = u) :
  subst s t = u := Eq.trans (congr_arg₂ SubTerm.subst es et) h

lemma shift_congr_eq {t t' : SyntacticSubTerm L n} {u} (e : t = t') (h : shift t' = u) :
  shift t = u := Eq.trans (congr_arg _ e) h

lemma bShift_congr_eq {t t' : SubTerm L μ n} {u} (e : t = t') (h : bShift t' = u) :
  bShift t = u := Eq.trans (congr_arg _ e) h

section
variable [hz : L.Zero] [ho : L.One] [ha : L.Add]

@[simp] lemma free_natLit (z : ℕ) :
    free (natLit L z : SyntacticSubTerm L (n + 1)) = natLit L z :=
  by simp

@[simp] lemma subst_natLit {s} (z : ℕ) :
    subst s (natLit L z : SubTerm L μ (n + 1)) = natLit L z :=
  by simp

@[simp] lemma shift_natLit (z : ℕ) :
    shift (natLit L z : SyntacticSubTerm L n) = natLit L z :=
  by simp

@[simp] lemma bShift_natLit (z : ℕ) :
    bShift (natLit L z : SubTerm L μ n) = natLit L z :=
  by simp[bShift]

end
end lemmata

partial def resultFree {L : Q(Language.{u})} {n : Q(ℕ)} : (t : Q(SyntacticSubTerm $L ($n + 1))) →
    MetaM ((res : Q(SyntacticSubTerm $L $n)) × Q(SubTerm.free $t = $res))
  | ~q(#$x)                              => do
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
  | ~q(&$x)                              => do
    let z ← natAppFunQ Nat.succ x
    let e : Expr := q(SubTerm.free_fvar (L := $L) (n := $n) $x)
    return ⟨q(&$z), e⟩
  | ~q(SubTerm.func $f ![])              => pure ⟨q(SubTerm.func $f ![]), q(free_func0 $f)⟩
  | ~q(SubTerm.func $f ![$t])            => do
    let ⟨tn, e⟩ ← resultFree (L := L) (n := n) t
    return ⟨q(SubTerm.func $f ![$tn]), q(free_func1 $f $e)⟩
  | ~q(SubTerm.func $f ![$t₁, $t₂])      => do
    let ⟨tn₁, e₁⟩ ← resultFree (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← resultFree (L := L) (n := n) t₂
    return ⟨q(SubTerm.func $f ![$tn₁, $tn₂]), q(free_func2 $f $e₁ $e₂)⟩
  | ~q(SubTerm.func $f ![$t₁, $t₂, $t₃]) => do
    let ⟨tn₁, e₁⟩ ← resultFree (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← resultFree (L := L) (n := n) t₂
    let ⟨tn₃, e₃⟩ ← resultFree (L := L) (n := n) t₃
    return ⟨q(SubTerm.func $f ![$tn₁, $tn₂, $tn₃]), q(free_func3 $f $e₁ $e₂ $e₃)⟩
  | ~q(SubTerm.Abbrev.const $ natLit (hz := $hz) (ho := $ho) (ha := $ha) $z) => pure ⟨q(natLit $L $z), q(free_natLit $z)⟩
  | ~q($t)                               => do
    return ⟨q(SubTerm.free $t), q(rfl)⟩

partial def resultSubst {L : Q(Language.{u})} {n : Q(ℕ)} (s : Q(SyntacticSubTerm $L $n)) :
    (t : Q(SyntacticSubTerm $L ($n + 1))) →
    MetaM ((res : Q(SyntacticSubTerm $L $n)) × Q(SubTerm.subst $s $t = $res))
  | ~q(#$x)                              => do
    let n ←whnf n 
    let some nval := n.natLit? | throwError f!"Fail: natLit: {n}"
    let some xval := (← finQVal (n := q(.succ $n)) x) | throwError f!"Fail: FinQVal {x}"
    if xval = nval then
      return ⟨q($s), (q(subst_bvar_last $n $s) : Expr)⟩
    else
      let lt ← decideTQ q(($x).val < $n)
      let e := q(free_bvar_of_lt (L := $L) $x $lt)
      let z : Q(Fin $n) ← Lean.Expr.ofNat q(Fin $n) xval
      return ⟨q(#$z), e⟩
  | ~q(&$x)                              => pure ⟨q(&$x), q(SubTerm.subst_fvar _ _)⟩
  | ~q(SubTerm.func $f ![])              => pure ⟨q(SubTerm.func $f ![]), q(subst_func0 $f)⟩
  | ~q(SubTerm.func $f ![$t])            => do
    let ⟨tn, e⟩ ← resultSubst (L := L) (n := n) s t
    return ⟨q(SubTerm.func $f ![$tn]), q(subst_func1 $f $e)⟩
  | ~q(SubTerm.func $f ![$t₁, $t₂])      => do
    let ⟨tn₁, e₁⟩ ← resultSubst (L := L) (n := n) s t₁
    let ⟨tn₂, e₂⟩ ← resultSubst (L := L) (n := n) s t₂
    return ⟨q(SubTerm.func $f ![$tn₁, $tn₂]), q(subst_func2 $f $e₁ $e₂)⟩
  | ~q(SubTerm.func $f ![$t₁, $t₂, $t₃]) => do
    let ⟨tn₁, e₁⟩ ← resultSubst (L := L) (n := n) s t₁
    let ⟨tn₂, e₂⟩ ← resultSubst (L := L) (n := n) s t₂
    let ⟨tn₃, e₃⟩ ← resultSubst (L := L) (n := n) s t₃
    return ⟨q(SubTerm.func $f ![$tn₁, $tn₂, $tn₃]), q(subst_func3 $f $e₁ $e₂ $e₃)⟩
  | ~q(SubTerm.Abbrev.const $ natLit (hz := $hz) (ho := $ho) (ha := $ha) $z) => pure ⟨q(natLit $L $z), q(subst_natLit $z)⟩
  | ~q($t)                               => do
    return ⟨q(SubTerm.subst $s $t), q(rfl)⟩

partial def resultShift {L : Q(Language.{u})} {n : Q(ℕ)} : (t : Q(SyntacticSubTerm $L $n)) →
    MetaM ((res : Q(SyntacticSubTerm $L $n)) × Q(SubTerm.shift $t = $res))
  | ~q(#$x)                              => pure ⟨q(#$x), q(SubTerm.shift_bvar $x)⟩
  | ~q(&$x)                              =>  do
    let z ← natAppFunQ Nat.succ x
    let e := q(SubTerm.shift_fvar (L := $L) (n := $n) $x)
    return ⟨q(&$z), e⟩
  | ~q(SubTerm.func $f ![])              => pure ⟨q(SubTerm.func $f ![]), q(shift_func0 $f)⟩
  | ~q(SubTerm.func $f ![$t])            => do
    let ⟨tn, e⟩ ← resultShift (L := L) (n := n) t
    return ⟨q(SubTerm.func $f ![$tn]), q(shift_func1 $f $e)⟩
  | ~q(SubTerm.func $f ![$t₁, $t₂])      => do
    let ⟨tn₁, e₁⟩ ← resultShift (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← resultShift (L := L) (n := n) t₂
    return ⟨q(SubTerm.func $f ![$tn₁, $tn₂]), q(shift_func2 $f $e₁ $e₂)⟩
  | ~q(SubTerm.func $f ![$t₁, $t₂, $t₃]) => do
    let ⟨tn₁, e₁⟩ ← resultShift (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← resultShift (L := L) (n := n) t₂
    let ⟨tn₃, e₃⟩ ← resultShift (L := L) (n := n) t₃
    return ⟨q(SubTerm.func $f ![$tn₁, $tn₂, $tn₃]), q(shift_func3 $f $e₁ $e₂ $e₃)⟩
  | ~q(SubTerm.subst $t₁ $t₂)            => do
    let ⟨tn₁, e₁⟩ ← resultShift (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← resultShift (L := L) (n := q(.succ $n)) t₂
    return ⟨q(SubTerm.subst $tn₁ $tn₂), q(shift_subst $e₂ $e₁)⟩
  | ~q(SubTerm.Abbrev.const $ natLit (hz := $hz) (ho := $ho) (ha := $ha) $z) => pure ⟨q(natLit $L $z), q(shift_natLit $z)⟩
  | ~q($t)                               => do
    return ⟨q(shift $t), q(rfl)⟩

partial def resultBShift {L : Q(Language.{u})} {n : Q(ℕ)} : (t : Q(SyntacticSubTerm $L $n)) →
    MetaM ((res : Q(SyntacticSubTerm $L ($n + 1))) × Q(bShift $t = $res))
  | ~q(#$x)                              => do
    let z ← natAppFunQ Nat.succ x
    let e := q(SubTerm.bShift_bvar (L := $L) (μ := ℕ) (n := $n) $x)
    return ⟨q(&$z), e⟩
  | ~q(&$x)                              => pure ⟨q(&$x), q(SubTerm.bShift_fvar $x)⟩
  | ~q(SubTerm.func $f ![])              => pure ⟨q(SubTerm.func $f ![]), q(bShift_func0 $f)⟩
  | ~q(SubTerm.func $f ![$t])            => do
    let ⟨tn, e⟩ ← resultBShift (L := L) (n := n) t
    return ⟨q(SubTerm.func $f ![$tn]), q(bShift_func1 $f $e)⟩
  | ~q(SubTerm.func $f ![$t₁, $t₂])      => do
    let ⟨tn₁, e₁⟩ ← resultBShift (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← resultBShift (L := L) (n := n) t₂
    return ⟨q(SubTerm.func $f ![$tn₁, $tn₂]), q(bShift_func2 $f $e₁ $e₂)⟩
  | ~q(SubTerm.func $f ![$t₁, $t₂, $t₃]) => do
    let ⟨tn₁, e₁⟩ ← resultBShift (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← resultBShift (L := L) (n := n) t₂
    let ⟨tn₃, e₃⟩ ← resultBShift (L := L) (n := n) t₃
    return ⟨q(SubTerm.func $f ![$tn₁, $tn₂, $tn₃]), q(bShift_func3 $f $e₁ $e₂ $e₃)⟩
  | ~q(SubTerm.subst $t₁ $t₂)            => do
    let ⟨tn₁, e₁⟩ ← resultBShift (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← resultBShift (L := L) (n := q(.succ $n)) t₂
    return ⟨q(SubTerm.subst $tn₁ $tn₂), q(bShift_subst $e₂ $e₁)⟩
  | ~q(SubTerm.Abbrev.const $ natLit (hz := $hz) (ho := $ho) (ha := $ha) $z) => pure ⟨q(natLit $L $z), q(bShift_natLit $z)⟩
  | ~q($t)                               => do
    return ⟨q(bShift $t), q(rfl)⟩

inductive TransparencyMode
  | constants
  | unfold  
  | all

partial def natLitResult {L : Q(Language.{u})}
  (iz : Q(Language.Zero $L)) (io : Q(Language.One $L)) (ia : Q(Language.Add $L)) (n : Q(ℕ)) :
    TransparencyMode → (z : Q(ℕ)) → MetaM $ (res : Q(SyntacticSubTerm $L $n)) × Q(natLit $L $z = $res)
  | TransparencyMode.constants =>
    fun z => do
    return ⟨q(natLit $L $z), q(rfl)⟩
  | TransparencyMode.unfold    =>
    fun z =>
      match z with
      | ~q(0)      => return ⟨q(natLit $L 0), q(rfl)⟩
      | ~q($z + 1) => do
        return ⟨q(func Language.Add.add ![natLit $L $z, func Language.One.one ![]]), q(rfl)⟩
      | ~q($z)      => return ⟨q(natLit $L $z), q(rfl)⟩
  | TransparencyMode.all       =>
    fun z =>
      match z with
      | ~q(0)      => return ⟨q(natLit $L 0), q(rfl)⟩
      | ~q($z + 1) => do
        let ⟨e, he⟩ ← natLitResult iz io ia n TransparencyMode.all z
        return ⟨q(func Language.Add.add ![$e, func Language.One.one ![]]), q(natLit_succ_of_eq $he)⟩
      | ~q($z)      => return ⟨q(natLit $L $z), q(rfl)⟩

partial def result (tp : TransparencyMode) {L : Q(Language.{u})} {n : Q(ℕ)} : (t : Q(SyntacticSubTerm $L $n)) →
    MetaM ((res : Q(SyntacticSubTerm $L $n)) × Q($t = $res))
  | ~q(#$x)                                           => pure ⟨q(#$x), q(rfl)⟩
  | ~q(&$x)                                           => pure ⟨q(&$x), q(rfl)⟩
  | ~q(SubTerm.func $f ![])                           => pure ⟨q(SubTerm.func $f ![]), q(rfl)⟩
  | ~q(SubTerm.func $f ![$t])                         => do
    let ⟨tn, e⟩ ← result tp (L := L) (n := n) t
    return ⟨q(SubTerm.func $f ![$tn]), q(func1_congr $f $e)⟩
  | ~q(SubTerm.func $f ![$t₁, $t₂])                   => do
    let ⟨tn₁, e₁⟩ ← result tp (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← result tp (L := L) (n := n) t₂
    return ⟨q(SubTerm.func $f ![$tn₁, $tn₂]), q(func2_congr $f $e₁ $e₂)⟩
  | ~q(SubTerm.func $f ![$t₁, $t₂, $t₃])              => do
    let ⟨tn₁, e₁⟩ ← result tp (L := L) (n := n) t₁
    let ⟨tn₂, e₂⟩ ← result tp (L := L) (n := n) t₂
    let ⟨tn₃, e₃⟩ ← result tp (L := L) (n := n) t₃
    return ⟨q(SubTerm.func $f ![$tn₁, $tn₂, $tn₃]), q(func3_congr $f $e₁ $e₂ $e₃)⟩
  | ~q(free $t)                                       => do
    let ⟨tn, e⟩ ← result tp (L := L) (n := q(.succ $n)) t
    let ⟨tnn, ee⟩ ← resultFree (L := L) (n := n) tn
    return ⟨q($tnn), q(free_congr_eq $e $ee)⟩
  | ~q(subst $s $t)                                   => do
    let ⟨tn, te⟩ ← result tp (L := L) (n := q(.succ $n)) t
    let ⟨sn, se⟩ ← result tp (L := L) (n := q($n)) s
    let ⟨tnn, ee⟩ ← resultSubst (L := L) (n := n) sn tn
    return ⟨q($tnn), q(subst_congr_eq $se $te $ee)⟩
  | ~q(shift $t)                                      => do
    let ⟨tn, e⟩ ← result tp (L := L) (n := q($n)) t
    let ⟨tnn, ee⟩ ← resultShift (L := L) (n := n) tn
    return ⟨q($tnn), q(shift_congr_eq $e $ee)⟩
  | ~q(SubTerm.Abbrev.const $ natLit (hz := $hz) (ho := $ho) (ha := $ha) $z) => natLitResult hz ho ha n tp z
  | ~q($t)                                            => pure ⟨q($t), q(rfl)⟩

partial def result' {L : Q(Language.{u})} {n : Q(ℕ)} (t : Q(SyntacticSubTerm $L $n))
  (tp : TransparencyMode := TransparencyMode.constants) :
    MetaM (Result (u := u) t) := do
    let ⟨res, e⟩ ← result tp t
    return ⟨res, e⟩

private inductive ResultTest (α : Type u) : (a : α) → Type u
  | result : (a b : α) → a = b → ResultTest α a

elab "dbg" : tactic => do
  let goalType ← Elab.Tactic.getMainTarget
  let some ⟨.succ u, ty⟩ ← checkSortQ' goalType | throwError "error: not a type"
  let ~q(ResultTest (SyntacticSubTerm $L $n) $t) := ty | throwError "error: not a type"
  logInfo m!"t = {t}"
  let t : Q(SyntacticSubTerm $L $n) ← withReducible <| whnf t

  let ⟨tn, e⟩ ← result TransparencyMode.unfold (L := L) (n := n) t
  logInfo m!"tn = {tn}"
  logInfo m!"e = {e}"
  let c : Q(ResultTest (SyntacticSubTerm $L $n) $t) := (q(ResultTest.result ($t) $tn $e) : Expr)
  Lean.Elab.Tactic.closeMainGoal c

example {t : SyntacticSubTerm Language.oring 13} : ResultTest (SyntacticSubTerm Language.oring 12)
    (shift $ subst &99 T“(!t) + (#6 * !(bShift T“#2 + 9”)) + &7”) :=
  by dbg

example {t : SyntacticSubTerm Language.oring 13} (z : ℕ) : ResultTest (SyntacticSubTerm Language.oring 12)
    (shift $ subst &99 T“!(shift $ natLit 8)”) :=
  by dbg

example : 1 ≠ 2 := of_decide_eq_true rfl

end Meta

end SubTerm
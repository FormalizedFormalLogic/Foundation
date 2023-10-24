import Logic.Predicate.FirstOrder.Principia.Term

open Qq Lean Elab Meta Tactic

-- Subformula normalization

namespace LO

namespace FirstOrder

namespace Principia

namespace lemmataFormula

variable {L : Language.{u}} {μ : Type v} {n}

open Subformula

lemma rel_ext {k} (r : L.rel k) (v w : Fin k → Subterm L μ₁ n₁) (H : ∀ i, v i = w i) :
    rel r v = rel r w := congr_arg _ (funext H)

lemma nrel_ext {k} (r : L.rel k) (v w : Fin k → Subterm L μ₁ n₁) (H : ∀ i, v i = w i) :
    nrel r v = nrel r w := congr_arg _ (funext H)

lemma finitary_ext {k} (f : Finitary L k) (v w : Fin k → Subterm L μ n) (H : ∀ i, v i = w i) :
    f.operator v = f.operator w := congr_arg _ (funext H)

section Rew

variable (ω : Rew L μ₁ n₁ μ₂ n₂)

lemma rew_rel_eq_of_eq {k} (r : L.rel k) {v : Fin k → Subterm L μ₁ n₁} {v'} (h : ∀ i, ω (v i) = v' i) :
    ω.hom (rel r v) = rel r v' :=
  by simp[Rew.rel, Function.comp, h]

lemma rew_nrel_eq_of_eq {k} (r : L.rel k) {v : Fin k → Subterm L μ₁ n₁} {v'} (h : ∀ i, ω (v i) = v' i) :
    ω.hom (nrel r v) = nrel r v' :=
  by simp[Rew.nrel, Function.comp, h]

lemma rew_const_eq_of_eq (c : Const L) :
    ω.hom (Operator.const c) = Operator.const c :=
  Rew.hom_const ω c

lemma rew_finitary_eq_of_eq {k} (f : Finitary L k) {v : Fin k → Subterm L μ₁ n₁} {v'} (h : ∀ i, ω (v i) = v' i) :
    ω.hom (f.operator v) = f.operator v' :=
  by simp[Rew.hom_operator, Function.comp, h]



end Rew

lemma shift_substs_eq_of_eq {t : SyntacticSubterm L k} {w : Fin k → SyntacticSubterm L n} {t' w'}
  (ht : Rew.shift t = t') (hw : ∀ i, Rew.shift (w i) = w' i) :
    Rew.shift (Rew.substs w t) = Rew.substs w' t' := by
  simp[←ht, ←hw, ←Rew.comp_app, Rew.shift_comp_substs]
  congr; funext i; simp[hw]

lemma subst_bshift_0 (v : Fin 1 → Subterm L μ 0) (t : Subterm L μ 0) : Rew.substs v (Rew.bShift t) = t := by simp[Rew.comp]

end lemmataFormula

inductive DFormula (L : Q(Language.{u})) : ℕ → Type
  | verum {n} : DFormula L n
  | falsum {n} : DFormula L n
  | rel {n arity : ℕ} : Q(($L).rel $arity) → (Fin arity → DTerm L n) → DFormula L n
  | nrel {n arity : ℕ} : Q(($L).rel $arity) → (Fin arity → DTerm L n) → DFormula L n
  | const {n} (c : Q(Subformula.Const.{u, 0} $L)) : DFormula L n
  | finitary {n arity : ℕ} (f : Q(Subformula.Finitary.{u, 0} $L $arity)) : (Fin arity → DTerm L n) → DFormula L n
  | and {n} : DFormula L n → DFormula L n → DFormula L n
  | or  {n} : DFormula L n → DFormula L n → DFormula L n
  | neg {n} : DFormula L n → DFormula L n
  | imply {n} : DFormula L n → DFormula L n → DFormula L n
  | iff {n} : DFormula L n → DFormula L n → DFormula L n
  | all {n} : DFormula L (n + 1) → DFormula L n
  | ex {n} : DFormula L (n + 1) → DFormula L n
  | expr {n : ℕ} : Q(SyntacticSubformula $L $n) → DFormula L n

namespace DFormula

instance : Inhabited (DFormula L n) := ⟨verum⟩

def toStr {L : Q(Language.{u})} {n : ℕ} : DFormula L n → String
  | verum        => "⊤"
  | falsum       => "⊥"
  | rel _ v      => "rel " ++ "(" ++ (String.vecToStr fun i => (v i).toStr) ++ ")"
  | nrel _ v     => "nrel " ++ "(" ++ (String.vecToStr fun i => (v i).toStr) ++ ")"
  | const _      => "const"
  | finitary _ v => "finitary " ++ "(" ++ (String.vecToStr fun i => (v i).toStr) ++ ")"
  | and p q      => "(" ++ p.toStr ++ ") ∧ (" ++ q.toStr ++ ")"
  | or p q       => "(" ++ p.toStr ++ ") ∨ (" ++ q.toStr ++ ")"
  | neg p        => "¬(" ++ p.toStr ++ ")"
  | imply p q    => "(" ++ p.toStr ++ ") → (" ++ q.toStr ++ ")"
  | iff p q      => "(" ++ p.toStr ++ ") ↔ (" ++ q.toStr ++ ")"
  | all p        => "∀[" ++ p.toStr ++ "]"
  | ex p         => "∃[" ++ p.toStr ++ "]"
  | expr _       => "expr"

instance : Repr (DTerm L n) := ⟨fun t _ => DTerm.toStr t⟩

instance : ToString (DTerm L n) := ⟨DTerm.toStr⟩

@[reducible] def toExpr {L : Q(Language.{u})} {n : ℕ} :
    DFormula L n → Q(SyntacticSubformula $L $n)
  | verum        => q(⊤)
  | falsum       => q(⊥)
  | rel r v      =>
    let w := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
    q(Subformula.rel $r $w)
  | nrel r v     =>
    let w := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
    q(Subformula.nrel $r $w)
  | const c      => q(Subformula.Operator.const $c)
  | finitary f v =>
    let w := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
    q(Subformula.Operator.operator $f $w)
  | and p q      => q($p.toExpr ⋏ $q.toExpr)
  | or p q       => q($p.toExpr ⋎ $q.toExpr)
  | neg p        => q(~$p.toExpr)
  | imply p q    => q($p.toExpr ⟶ $q.toExpr)
  | iff p q      => q($p.toExpr ⟷ $q.toExpr)
  | all p        => q(∀' $p.toExpr)
  | ex p         => q(∃' $p.toExpr)
  | expr e       => e

protected def isDefEq {L : Q(Language.{u})} {n} (p₁ p₂ : DFormula L n) : MetaM Bool :=
  Lean.Meta.isDefEq p₁.toExpr p₂.toExpr

partial def denote (L : Q(Language.{u})) (n : ℕ) : (p : Q(SyntacticSubformula $L $n)) → MetaM (DFormula L n)
  | ~q(⊤) => pure verum
  | ~q(⊥) => pure falsum
  | ~q(Subformula.rel (arity := $arity) $r $v)  => do
    let arity' : ℕ ← Denotation.denote arity
    let v' ← vecUnfold q(SyntacticSubterm $L $n) arity' v
    let v'' ← Matrix.getM fun i => DTerm.denote L n (v' i)
    return rel r v''
  | ~q(Subformula.nrel (arity := $arity) $r $v) => do
    let arity' : ℕ ← Denotation.denote arity
    let v' ← vecUnfold q(SyntacticSubterm $L $n) arity' v
    let v'' ← Matrix.getM fun i => DTerm.denote L n (v' i)
    return nrel r v''
  | ~q(Subformula.Operator.const $c)                         => pure (const c)
  | ~q(Subformula.Operator.operator (ι := Fin $arity) $r $v) => do
    let arity' : ℕ ← Denotation.denote arity
    let v' ← vecUnfold q(SyntacticSubterm $L $n) arity' v
    let v'' ← Matrix.getM fun i => DTerm.denote L n (v' i)
    return finitary r v''
  | ~q($p ⋏ $q)  => return and (←denote L n p) (←denote L n q)
  | ~q($p ⋎ $q)  => return or (←denote L n p) (←denote L n q)
  | ~q(~$p)      => return neg (←denote L n p)
  | ~q($p ⟶ $q) => return imply (←denote L n p) (←denote L n q)
  | ~q($p ⟷ $q)  => return iff (←denote L n p) (←denote L n q)
  | ~q(∀' $p)    => return all (←denote L (n + 1) p)
  | ~q(∃' $p)    => return ex (←denote L (n + 1) p)
  | ~q($p)       => return expr p

instance (L : Q(Language.{u})) (n) : Denotation (DFormula L n) where
  denote := denote L n
  toExpr := toExpr

structure DEq {L : Q(Language.{u})} {n : ℕ} (p₁ p₂ : DFormula L n) where
  expr : Q($(p₁.toExpr) = $(p₂.toExpr))

local infix:20 " ≡ " => DFormula.DEq

namespace DEq

variable {L : Q(Language.{u})} {n : ℕ}


@[refl] protected def refl (p : DFormula L n) : p ≡ p := .mk q(rfl)

@[symm] protected def symm {p₁ p₂ : DFormula L n} (h : p₁ ≡ p₂) : p₂ ≡ p₁ :=
  .mk q(Eq.symm $h.expr)

@[trans] protected def trans {p₁ p₂ p₃ : DFormula L n} (h₁ : p₁ ≡ p₂) (h₂ : p₂ ≡ p₃) : p₁ ≡ p₃ :=
  .mk q(Eq.trans $h₁.expr $h₂.expr)

def ofIsDefEq (p₁ p₂ : DFormula L n) : p₁ ≡ p₂ := ⟨(q(@rfl (SyntacticSubformula $L $n) $p₁.toExpr) : Expr)⟩

def relExt {arity : ℕ} (r : Q(($L).rel $arity)) {v w : Fin arity → DTerm L n} (H : (i : Fin arity) → (v i).DEq (w i)) :
    rel r v ≡ rel r w := by
  let v' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
  let w' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (w i).toExpr)
  let H : Q(∀ i, $v' i = $w' i) := vecFoldDep q(fun i => $v' i = $w' i) (fun i => (H i).expr)
  let e : Q(Subformula.rel $r $v' = Subformula.rel $r $w') := q(lemmataFormula.rel_ext $r _ _ $H)
  exact .mk e

def nrelExt {arity : ℕ} (r : Q(($L).rel $arity)) {v w : Fin arity → DTerm L n} (H : (i : Fin arity) → (v i).DEq (w i)) :
    nrel r v ≡ nrel r w := by
  let v' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
  let w' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (w i).toExpr)
  let H : Q(∀ i, $v' i = $w' i) := vecFoldDep q(fun i => $v' i = $w' i) (fun i => (H i).expr)
  let e : Q(Subformula.nrel $r $v' = Subformula.nrel $r $w') := q(lemmataFormula.nrel_ext $r _ _ $H)
  exact .mk e

def finitaryExt {arity : ℕ}
  (f : Q(Subformula.Finitary.{u, 0} $L $arity)) {v w : Fin arity → DTerm L n} (H : (i : Fin arity) → (v i).DEq (w i)) :
    finitary f v ≡ finitary f w := by
  let v' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
  let w' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (w i).toExpr)
  let H : Q(∀ i, $v' i = $w' i) := vecFoldDep q(fun i => $v' i = $w' i) (fun i => (H i).expr)
  let e : Q(($f).operator $v' = ($f).operator $w') := q(lemmataFormula.finitary_ext $f _ _ $H)
  exact .mk e

end DEq

abbrev qrew (L : Q(Language.{u})) (n m: ℕ) (ω : Q(Rew $L ℕ $n ℕ $m)) : Q(SyntacticSubformula $L $n → SyntacticSubformula $L $m) := q(($ω).hom)

abbrev qsubsts {L : Q(Language.{u})} {arity n : ℕ} (v : Fin arity → DTerm L n) :
    Q(SyntacticSubformula $L $arity → SyntacticSubformula $L $n) :=
  let v' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
  qrew L arity n q(Rew.substs $v')

abbrev qshift {L : Q(Language.{u})} {n : ℕ} : Q(SyntacticSubformula $L $n → SyntacticSubformula $L $n) :=
  qrew L n n q(Rew.shift)

abbrev qbShift {L : Q(Language.{u})} {n : ℕ} : Q(SyntacticSubformula $L $n → SyntacticSubformula $L ($n + 1)) :=
  qrew L n (n + 1) q(Rew.bShift)

abbrev qfix {L : Q(Language.{u})} {n : ℕ} : Q(SyntacticSubformula $L $n → SyntacticSubformula $L ($n + 1)) :=
  qrew L n (n + 1) q(Rew.fix)

abbrev qfree {L : Q(Language.{u})} {n : ℕ} : Q(SyntacticSubformula $L ($n + 1) → SyntacticSubformula $L $n) :=
  qrew L (n + 1) n q(Rew.free)

structure DEqFun {L : Q(Language.{u})} {n₁ n₂ : ℕ} (f : Q(SyntacticSubformula $L $n₁ → SyntacticSubformula $L $n₂))
  (p₁ : DFormula L n₁) (p₂ : DFormula L n₂) where
  expr : Q($f $(p₁.toExpr) = $(p₂.toExpr))

local notation:25 p₁ " ≡[" f:25 "] " p₂:0 => DEqFun f p₁ p₂

namespace DEqFun

variable {L : Q(Language.{u})} {n : ℕ}

def ofDEqFunOfDEq {n₁ n₂ : ℕ} {f : Q(SyntacticSubformula $L $n₁ → SyntacticSubformula $L $n₂)}
  {p₁ : DFormula L n₁} {p₂ p₂' : DFormula L n₂} (df : p₁ ≡[f] p₂) (de : p₂ ≡ p₂') :
    p₁ ≡[f] p₂' := ⟨q(Eq.trans $df.expr $de.expr)⟩

def rewRel {arity n m : ℕ} (ω : Q(Rew $L ℕ $n ℕ $m)) (r : Q(($L).rel $arity))
  {v : Fin arity → DTerm L n} {w : Fin arity → DTerm L m}
  (H : ∀ i, DTerm.DEqFun (DTerm.qrew L n m ω) (v i) (w i)) : rel r v ≡[qrew L n m ω] rel r w := by
  let v' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
  let w' := Qq.vecFold q(SyntacticSubterm $L $m) (fun i => (w i).toExpr)
  let H : Q(∀ i, $ω ($v' i) = $w' i) := vecFoldDep q(fun i => $ω ($v' i) = $w' i) (fun i => (H i).expr)
  let e : Q(($ω).hom (Subformula.rel $r $v') = Subformula.rel $r $w') := q(lemmataFormula.rew_rel_eq_of_eq _ $r $H)
  exact .mk e

def rewNrel {arity n m : ℕ} (ω : Q(Rew $L ℕ $n ℕ $m)) (r : Q(($L).rel $arity))
  {v : Fin arity → DTerm L n} {w : Fin arity → DTerm L m}
  (H : ∀ i, DTerm.DEqFun (DTerm.qrew L n m ω) (v i) (w i)) : nrel r v ≡[qrew L n m ω] nrel r w := by
  let v' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
  let w' := Qq.vecFold q(SyntacticSubterm $L $m) (fun i => (w i).toExpr)
  let H : Q(∀ i, $ω ($v' i) = $w' i) := vecFoldDep q(fun i => $ω ($v' i) = $w' i) (fun i => (H i).expr)
  let e : Q(($ω).hom (Subformula.nrel $r $v') = Subformula.nrel $r $w') := q(lemmataFormula.rew_nrel_eq_of_eq _ $r $H)
  exact .mk e

def rewFinitary {arity n m : ℕ} (ω : Q(Rew $L ℕ $n ℕ $m))
  (f : Q(Subformula.Finitary.{u, 0} $L $arity)) {v : Fin arity → DTerm L n} {w : Fin arity → DTerm L m}
  (H : ∀ i, DTerm.DEqFun (DTerm.qrew L n m ω) (v i) (w i)) : finitary f v ≡[qrew L n m ω] finitary f w := by
  let v' := Qq.vecFold q(SyntacticSubterm $L $n) (fun i => (v i).toExpr)
  let w' := Qq.vecFold q(SyntacticSubterm $L $m) (fun i => (w i).toExpr)
  let H : Q(∀ i, $ω ($v' i) = $w' i) := vecFoldDep q(fun i => $ω ($v' i) = $w' i) (fun i => (H i).expr)
  let e : Q(($ω).hom (($f).operator $v') = ($f).operator $w') := q(lemmataFormula.rew_finitary_eq_of_eq _ $f $H)
  exact .mk e

def rewConst {n m : ℕ} (ω : Q(Rew $L ℕ $n ℕ $m))
  (c : Q(Subformula.Const.{u, 0} $L)) : (const c : DFormula L n) ≡[qrew L n m ω] const c := by
  let e : Q(($ω).hom (Subformula.Operator.const $c) = Subformula.Operator.const $c) := q(lemmataFormula.rew_const_eq_of_eq _ $c)
  exact .mk e

end DEqFun


end DFormula

end Principia

end FirstOrder

end LO

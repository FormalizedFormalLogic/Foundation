import Logic.Predicate.FirstOrder.Deduction.Deduction
import Logic.Predicate.FirstOrder.Meta

open Qq Lean Elab Meta Tactic Term

namespace FirstOrder

namespace Deduction
open SubFormula
variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)] [L.Eq]
variable {T : Theory L} [EqTheory T]
variable {Δ : List (SyntacticFormula L)}

def generalizeOfEq {Δ Δ' p p'}
  (hΔ : Δ.map shift = Δ') (hp : free p = p') (b : Δ' ⟹[T] p') : Δ ⟹[T] ∀' p :=
  generalize (b.cast' hΔ.symm hp.symm)

def specializeOfEq (t) {Δ p p'}
  (hp : ⟦↦ t⟧ p = p') (b : Δ ⟹[T] ∀' p) : Δ ⟹[T] p' :=
  (b.specialize t).cast hp

def exCasesOfEq {Δ Δ' p p' q q'}
  (hΔ : Δ.map shift = Δ') (hp : free p = p') (hq : shift q = q')
  (b₀ : Δ ⟹[T] ∃' p) (b₁ : (p' :: Δ') ⟹[T] q') : Δ ⟹[T] q :=
  b₀.exCases (b₁.cast' (by rw[hΔ, hp]) hq.symm)

def useInstanceOfEq (t) {Δ p p'} (h : ⟦↦ t⟧ p = p')
  (b : Δ ⟹[T] p') : Δ ⟹[T] ∃' p :=
  useInstance t (b.cast h.symm)

def weakening {Δ Γ p} (h : Δ ⊆ Γ) (b : Δ ⟹[T] p) : Γ ⟹[T] p :=
  b.weakening' (List.cons_subset_cons _ h)

protected def shift {p} (b : Δ ⟹[T] p) : (Δ.map shift) ⟹[T] shift p :=
  b.rewrite _

def absurd {p} (b : (p :: Δ) ⟹[T] ⊥) : Δ ⟹[T] ~p :=
  (contradiction (~p) trivial b).weakening' (by simp)

def splitIff {p q} (b₁ : Δ ⟹[T] p ⟶ q) (b₂ : Δ ⟹[T] q ⟶ p) : Δ ⟹[T] p ⟷ q :=
  split b₁ b₂

def modusPonensOfIffLeft {p q} (b₀ : Δ ⟹[T] p ⟷ q) (b₁ : Δ ⟹[T] p) : Δ ⟹[T] q :=
  b₀.andLeft.modusPonens b₁

def modusPonensOfIffRight {p q} (b₀ : Δ ⟹[T] p ⟷ q) (b₁ : Δ ⟹[T] q) : Δ ⟹[T] p :=
  b₀.andRight.modusPonens b₁

def iffRefl (p) : Δ ⟹[T] p ⟷ p := split (intro $ assumption $ by simp) (intro $ assumption $ by simp) 

def iffReflOfEq {p q} (h : p = q) : Δ ⟹[T] p ⟷ q := by rw [h]; exact iffRefl q

def iffSymm {p q} (b : Δ ⟹[T] p ⟷ q) : Δ ⟹[T] q ⟷ p :=
  b.andRight.split b.andLeft

def iffTrans {p q r} (b₁ : Δ ⟹[T] p ⟷ q) (b₂ : Δ ⟹[T] q ⟷ r) : Δ ⟹[T] p ⟷ r :=
  split
    (intro $ modusPonens (b₂.andLeft.weakening (by simp)) $
      modusPonens (b₁.andLeft.weakening (by simp)) $ assumption (by simp))
    (intro $ modusPonens (b₁.andRight.weakening (by simp)) $
      modusPonens (b₂.andRight.weakening (by simp)) $ assumption (by simp))

def iffAnd {p₁ p₂ q₁ q₂} (b₁ : Δ ⟹[T] p₁ ⟷ q₁) (b₂ : Δ ⟹[T] p₂ ⟷ q₂) : Δ ⟹[T] p₁ ⋏ p₂ ⟷ q₁ ⋏ q₂ :=
  splitIff
    (intro $ split
        ((b₁.andLeft.weakening (List.subset_cons_of_subset _ $ by simp[List.subset_cons])).modusPonens $ andLeft (q := p₂) (assumption $ by simp))
        ((b₂.andLeft.weakening (List.subset_cons_of_subset _ $ by simp[List.subset_cons])).modusPonens $ andRight (p := p₁) (assumption $ by simp)))
    (intro $ split
        ((b₁.andRight.weakening (List.subset_cons_of_subset _ $ by simp[List.subset_cons])).modusPonens $ andLeft (q := q₂) (assumption $ by simp))
        ((b₂.andRight.weakening (List.subset_cons_of_subset _ $ by simp[List.subset_cons])).modusPonens $ andRight (p := q₁) (assumption $ by simp)))

def iffOr {p₁ p₂ q₁ q₂} (b₁ : Δ ⟹[T] p₁ ⟷ q₁) (b₂ : Δ ⟹[T] p₂ ⟷ q₂) : Δ ⟹[T] p₁ ⋎ p₂ ⟷ q₁ ⋎ q₂ :=
  splitIff
    (intro $ cases (p := p₁) (q := p₂) (assumption $ by simp)
      (orLeft $ (b₁.andLeft.weakening (List.subset_cons_of_subset _ $ by simp[List.subset_cons])).modusPonens $ assumption $ by simp)
      (orRight $ (b₂.andLeft.weakening (List.subset_cons_of_subset _ $ by simp[List.subset_cons])).modusPonens $ assumption $ by simp))
    (intro $ cases (p := q₁) (q := q₂) (assumption $ by simp)
      (orLeft $ (b₁.andRight.weakening (List.subset_cons_of_subset _ $ by simp[List.subset_cons])).modusPonens $ assumption $ by simp)
      (orRight $ (b₂.andRight.weakening (List.subset_cons_of_subset _ $ by simp[List.subset_cons])).modusPonens $ assumption $ by simp))

def iffNeg {p q} (b : Δ ⟹[T] p ⟷ q) : Δ ⟹[T] ~p ⟷ ~q :=
  splitIff
    (intro $ absurd $ contradiction (p := p) ⊥
      ((b.andRight.weakening (List.subset_cons_of_subset _ $ by simp)).modusPonens $ assumption $ by simp)
      (assumption $ by simp))
    (intro $ absurd $ contradiction (p := q) ⊥
      ((b.andLeft.weakening (List.subset_cons_of_subset _ $ by simp)).modusPonens $ assumption $ by simp)
      (assumption $ by simp))

def iffAll {p q} (b : Δ.map shift ⟹[T] free p ⟷ free q) : Δ ⟹[T] ∀' p ⟷ ∀' q :=
  splitIff
    (intro $ generalize $ (b.andLeft.weakening $ by simp).modusPonens $
      (specialize &0 (p := shift p) $ assumption $ by simp).cast (by simp))
    (intro $ generalize $ (b.andRight.weakening $ by simp).modusPonens $
      (specialize &0 (p := shift q) $ assumption $ by simp).cast (by simp))

def iffEx {p q} (b : Δ.map shift ⟹[T] free p ⟷ free q) : Δ ⟹[T] ∃' p ⟷ ∃' q :=
  splitIff
    (intro $ exCases (p := p) (assumption $ by simp) $ (useInstance &0 (p := shift q) $
      ((b.andLeft.weakening (List.subset_cons_of_subset _ $ by simp)).modusPonens $ assumption $ by simp).cast (by simp)).cast (by simp))
    (intro $ exCases (p := q) (assumption $ by simp) $ (useInstance &0 (p := shift p) $
      ((b.andRight.weakening (List.subset_cons_of_subset _ $ by simp)).modusPonens $ assumption $ by simp).cast (by simp)).cast (by simp))

inductive IffFormula : (p₀ q₀ : SyntacticFormula L) → SyntacticFormula L → SyntacticFormula L → Type u
  | intro {p₀ q₀} : IffFormula p₀ q₀ p₀ q₀
  | refl {p₀ q₀} : (p : SyntacticFormula L) → IffFormula p₀ q₀ p p
  | and {p₀ q₀ p₁ p₂ q₁ q₂} : IffFormula p₀ q₀ p₁ q₁ → IffFormula p₀ q₀ p₂ q₂ → IffFormula p₀ q₀ (p₁ ⋏ p₂) (q₁ ⋏ q₂)
  | or {p₀ q₀ p₁ p₂ q₁ q₂} : IffFormula p₀ q₀ p₁ q₁ → IffFormula p₀ q₀ p₂ q₂ → IffFormula p₀ q₀ (p₁ ⋎ p₂) (q₁ ⋎ q₂)
  | all {p₀ q₀} {p q : SyntacticSubFormula L 1} : IffFormula (shift p₀) (shift q₀) (free p) (free q) → IffFormula p₀ q₀ (∀' p) (∀' q)
  | ex {p₀ q₀} {p q : SyntacticSubFormula L 1} : IffFormula (shift p₀) (shift q₀) (free p) (free q) → IffFormula p₀ q₀ (∃' p) (∃' q)

def iffOfIffFormula {p₀ q₀} :
    {p q : SyntacticFormula L} → IffFormula p₀ q₀ p q → {Δ : List (SyntacticFormula L)} → (Δ ⟹[T] p₀ ⟷ q₀) → (Δ ⟹[T] p ⟷ q)
  | _, _, IffFormula.intro,     _, b => b
  | _, _, IffFormula.refl p,    Δ, _ => iffRefl _
  | _, _, IffFormula.and h₁ h₂, Δ, b => iffAnd (iffOfIffFormula h₁ b) (iffOfIffFormula h₂ b)
  | _, _, IffFormula.or h₁ h₂,  Δ, b => iffOr (iffOfIffFormula h₁ b) (iffOfIffFormula h₂ b)
  | _, _, IffFormula.all h,     Δ, b => (iffOfIffFormula h (b.shift.cast $ by simp)).iffAll
  | _, _, IffFormula.ex h,      Δ, b => (iffOfIffFormula h (b.shift.cast $ by simp)).iffEx

def eqReflOfEq {t₁ t₂ : SyntacticTerm L} (h : t₁ = t₂) :
    Δ ⟹[T] “ᵀ!t₁ = ᵀ!t₂” := by rw[h]; exact eqRefl _

end Deduction

namespace Meta

namespace DeductionQ
open SubFormula
variable (L : Q(Language.{u}))
variable (dfunc : Q(∀ k, DecidableEq (($L).func k))) (drel : Q(∀ k, DecidableEq (($L).rel k))) (lEq : Q(Language.Eq $L)) 
variable (T : Q(Theory $L)) (eqTh : Q(EqTheory $T))
variable (Δ : Q(List (SyntacticFormula $L))) (Δ' : Q(List (SyntacticFormula $L)))

def assumptionQ (Γ : Q(List (SyntacticFormula $L))) (p : Q(SyntacticFormula $L)) (h : Q($p ∈ $Γ)) :
    Q($Γ ⟹[$T] $p) :=
  q(Deduction.assumption $h)

def generalizeOfEqQ (p : Q(SyntacticSubFormula $L 1)) (p' : Q(SyntacticFormula $L))
  (hΔ : Q(($Δ).map shift = $Δ')) (hp : Q(free $p = $p')) (b : Q($Δ' ⟹[$T] $p')) : Q($Δ ⟹[$T] ∀' $p) :=
  q(Deduction.generalizeOfEq $hΔ $hp $b)

def useInstanceOfEqQ (t : Q(SyntacticTerm $L)) (p : Q(SyntacticSubFormula $L 1)) (p' : Q(SyntacticFormula $L))
  (h : Q(⟦↦ $t⟧ $p = $p')) (b : Q($Δ ⟹[$T] $p')) : Q($Δ ⟹[$T] ∃' $p) :=
  q(Deduction.useInstanceOfEq $t $h $b)

def exCasesOfEqQ
  (p : Q(SyntacticSubFormula $L 1)) (p' : Q(SyntacticFormula $L))
  (q q' : Q(SyntacticFormula $L))
  (hΔ : Q(($Δ).map shift = $Δ')) (hp : Q(free $p = $p')) (hq : Q(shift $q = $q'))
  (b₀ : Q($Δ ⟹[$T] ∃' $p)) (b₁ : Q(($p' :: $Δ') ⟹[$T] $q')) : Q($Δ ⟹[$T] $q) :=
  q(Deduction.exCasesOfEq $hΔ $hp $hq $b₀ $b₁)

def eqReflOfEqQ (t₁ t₂ : Q(SyntacticTerm $L)) (h : Q($t₁ = $t₂)) :
    Q($Δ ⟹[$T] SubFormula.rel Language.Eq.eq ![$t₁, $t₂]) := q(Deduction.eqReflOfEq $h)

def iffReflOfEqQ (p₁ p₂ : Q(SyntacticFormula $L)) (h : Q($p₁ = $p₂)) :
    Q($Δ ⟹[$T] $p₁ ⟷ $p₂) := q(Deduction.iffReflOfEq $h)

end DeductionQ

section Syntax
variable (L : Q(Language.{u})) (n : Q(ℕ))
open SubTerm

-- TODO
partial def subTermSyntaxToExpr (n : Q(ℕ)) : Syntax → TermElabM Q(SyntacticSubTerm $L $n)
  | `(subterm| ($s)) => subTermSyntaxToExpr n s
  | `(subterm| ᵀ!$t:term) =>
    Term.elabTerm t (return q(SyntacticSubTerm $L $n))
  | `(subterm| $n:num) => do
    let en ← Term.elabTerm n (return q(ℕ))
    let _ ← synthInstanceQ q(Language.Zero $L)
    let _ ← synthInstanceQ q(Language.One $L)
    let _ ← synthInstanceQ q(Language.Add $L)
    let z : Q(ℕ) := en
    return q(SubTerm.Operator.const (natLit $L $z))
  | `(subterm| # $x:num) => do
    let some nval := (←whnf n).natLit? | throwError f!"Fail: natLit?: {n}"
    let xval ← Lean.Syntax.isNatLit? x
    if xval < nval then
      let ex : Q(Fin $n) ← Expr.ofNat q(Fin $n) xval
      return q(#$ex)
    else throwError "invalid variable: {xval} ≥ {n}"
  | `(subterm| & $x:num) => do
    let ex : Q(ℕ) ← Term.elabTerm x (return q(ℕ))
    return q(&$ex)
  | `(subterm| $t₁:subterm + $t₂:subterm) => do
    let et₁ ← subTermSyntaxToExpr n t₁
    let et₂ ← subTermSyntaxToExpr n t₂
    let (_ : Q(Language.Add $L)) ← synthInstanceQ q(Language.Add $L)
    return q(SubTerm.func Language.Add.add ![$et₁, $et₂])
  | `(subterm| $t₁:subterm * $t₂:subterm) => do
    let et₁ ← subTermSyntaxToExpr n t₁
    let et₂ ← subTermSyntaxToExpr n t₂
    let (_ : Q(Language.Mul $L)) ← synthInstanceQ q(Language.Mul $L)
    return q(SubTerm.func Language.Mul.mul ![$et₁, $et₂])
  | `(subterm| $t₁:subterm ^ $t₂:subterm) => do
    let et₁ ← subTermSyntaxToExpr n t₁
    let et₂ ← subTermSyntaxToExpr n t₂
    let (_ : Q(Language.Pow $L)) ← synthInstanceQ q(Language.Pow $L)
    return q(SubTerm.func Language.Pow.pow ![$et₁, $et₂])
  | `(subterm| $t ᵀ⟦$v:subterm,*⟧) => do
    let e0 : Q(Fin 0 → SyntacticSubTerm $L $n) := q(![])
    let (k, ev) ← v.getElems.foldlM (β := ℕ × Expr)
      (init := (0, (e0 : Expr)))
      (fun (k, e) s => do
        let ih : Q(Fin $k → SyntacticSubTerm $L $n) := e
        let es : Q(SyntacticSubTerm $L $n) ← subTermSyntaxToExpr n s
        let e : Q(Fin ($k + 1) → SyntacticSubTerm $L $n) := q($es :> $ih) 
        return (k + 1, e))
    let ev : Q(Fin $k → SyntacticSubTerm $L $n) := ev
    let et ← subTermSyntaxToExpr q($k) t
    return q(substs $ev $et)
  | _                    => throwUnsupportedSyntax
  
-- TODO
partial def subFormulaSyntaxToExpr (n : Q(ℕ)) : Syntax → TermElabM Q(SyntacticSubFormula $L $n)
  | `(subformula| ($p)) => subFormulaSyntaxToExpr n p
  | `(subformula| !$t:term)  =>
    Term.elabTerm t (return q(SyntacticSubFormula $L $n))

  | `(subformula| $t₁:subterm = $t₂:subterm) => do
    let et₁ ← subTermSyntaxToExpr L n t₁
    let et₂ ← subTermSyntaxToExpr L n t₂
    let (_ : Q(Language.Eq $L)) ← synthInstanceQ q(Language.Eq $L)
    let e : Expr := q(SubFormula.rel Language.Eq.eq ![$et₁, $et₂])
    return e
  | `(subformula| $t₁:subterm ≠ $t₂:subterm) => do
    let et₁ ← subTermSyntaxToExpr L n t₁
    let et₂ ← subTermSyntaxToExpr L n t₂
    let (_ : Q(Language.Eq $L)) ← synthInstanceQ q(Language.Eq $L)
    let e : Expr := q(SubFormula.nrel Language.Eq.eq ![$et₁, $et₂])
    return e

  | `(subformula| $t₁:subterm < $t₂:subterm) => do
    let et₁ ← subTermSyntaxToExpr L n t₁
    let et₂ ← subTermSyntaxToExpr L n t₂
    let (_ : Q(Language.Lt $L)) ← synthInstanceQ q(Language.Lt $L)
    let e : Expr := q(SubFormula.rel Language.Lt.lt ![$et₁, $et₂])
    return e
  | `(subformula| $t₁:subterm ≮ $t₂:subterm) => do
    let et₁ ← subTermSyntaxToExpr L n t₁
    let et₂ ← subTermSyntaxToExpr L n t₂
    let (_ : Q(Language.Lt $L)) ← synthInstanceQ q(Language.Lt $L)
    let e : Expr := q(SubFormula.nrel Language.Lt.lt ![$et₁, $et₂])
    return e

  | `(subformula| ⊤)       => return q(⊤)
  | `(subformula| ⊥)       => return q(⊥)
  | `(subformula| $p ∧ $q) => do
    let ep ← subFormulaSyntaxToExpr n p
    let eq ← subFormulaSyntaxToExpr n q
    let epandeq : Expr := q($ep ⋏ $eq)
    return epandeq
  | `(subformula| $p ∨ $q) => do
    let ep ← subFormulaSyntaxToExpr n p
    let eq ← subFormulaSyntaxToExpr n q
    let eporeq : Expr := q($ep ⋏ $eq)
    return eporeq
  | `(subformula| ∀ $p)     => do
    let ep ← subFormulaSyntaxToExpr q($n + 1) p
    let allep : Expr := q(∀' $ep)
    return allep
  | `(subformula| ∃ $p)     => do
    let ep ← subFormulaSyntaxToExpr q($n + 1) p
    let exep : Expr := q(∃' $ep)
    return exep

  | `(subformula| ¬$p)     => do
    let ep ← subFormulaSyntaxToExpr n p
    have nep : Expr := q(~$ep)
    return nep
  | `(subformula| $p → $q) => do
    let ep ← subFormulaSyntaxToExpr n p
    let eq ← subFormulaSyntaxToExpr n q
    let eptoeq : Expr := q($ep ⟶ $eq)
    return eptoeq
  | `(subformula| $p ↔ $q) => do
    let ep ← subFormulaSyntaxToExpr n p
    let eq ← subFormulaSyntaxToExpr n q
    let epiffeq : Expr := q($ep ⟷ $eq)
    return epiffeq
  | `(subformula| $p ⟦$v:subterm,*⟧) => do
    let e0 : Q(Fin 0 → SyntacticSubTerm $L $n) := q(![])
    let (k, ev) ← v.getElems.foldlM (β := ℕ × Expr)
      (init := (0, (e0 : Expr)))
      (fun (k, e) s => do
        let ih : Q(Fin $k → SyntacticSubTerm $L $n) := e
        let es : Q(SyntacticSubTerm $L $n) ← subTermSyntaxToExpr L n s
        let e : Q(Fin ($k + 1) → SyntacticSubTerm $L $n) := q($es :> $ih) 
        return (k + 1, e))
    let ev : Q(Fin $k → SyntacticSubTerm $L $n) := ev
    let ep ← subFormulaSyntaxToExpr q($k) p
    return q(SubFormula.substs $ev $ep)
  | _                   => throwUnsupportedSyntax

partial def termSyntaxToExpr (s : Syntax) : TermElabM Q(SyntacticTerm $L) :=
  subTermSyntaxToExpr L q(0) s

partial def formulaSyntaxToExpr (s : Syntax) : TermElabM Q(SyntacticFormula $L) :=
  subFormulaSyntaxToExpr L q(0) s

end Syntax

inductive DeductionCode (L : Q(Language.{u})) : Type
  | assumption    : DeductionCode L
  | trans         : Q(SyntacticFormula $L) → DeductionCode L → DeductionCode L → DeductionCode L
  | contradiction : Q(SyntacticFormula $L) → DeductionCode L → DeductionCode L → DeductionCode L
  | trivial       : DeductionCode L
  | explode       : DeductionCode L → DeductionCode L
  | intro         : DeductionCode L → DeductionCode L
  | modusPonens   : Q(SyntacticFormula $L) → DeductionCode L → DeductionCode L → DeductionCode L  
  | split         : DeductionCode L → DeductionCode L → DeductionCode L
  | andLeft       : Q(SyntacticFormula $L) → DeductionCode L → DeductionCode L
  | andRight      : Q(SyntacticFormula $L) → DeductionCode L → DeductionCode L
  | orLeft        : DeductionCode L → DeductionCode L
  | orRight       : DeductionCode L → DeductionCode L
  | cases         : (e₁ e₂ : Q(SyntacticFormula $L)) → DeductionCode L → DeductionCode L → DeductionCode L → DeductionCode L
  | generalize    : DeductionCode L → DeductionCode L
  | specialize    : Q(SyntacticTerm $L) → DeductionCode L → DeductionCode L
  | useInstance   : Q(SyntacticTerm $L) → DeductionCode L → DeductionCode L
  | exCases       : Q(SyntacticSubFormula $L 1) → DeductionCode L → DeductionCode L → DeductionCode L
  | eqRefl        : DeductionCode L
  | eqSymm        : DeductionCode L → DeductionCode L
  | eqTrans       : Q(SyntacticFormula $L) → DeductionCode L → DeductionCode L → DeductionCode L
  | rewriteEq     : (e₁ e₂ : Q(SyntacticTerm $L)) → DeductionCode L → DeductionCode L → DeductionCode L
  | since         : Syntax → DeductionCode L
  | rwEq          : Q(SyntacticTerm $L) → Syntax → DeductionCode L → DeductionCode L
  | showState     : DeductionCode L → DeductionCode L
  | missing       : DeductionCode L
  -- TODO

namespace DeductionCode
variable (L : Q(Language.{u}))

def toStr : DeductionCode L → String
  | assumption            => "assumption"
  | trans _ c₁ c₂         => "have: {\n" ++ c₁.toStr ++ "\n}" ++ c₂.toStr
  | contradiction _ c₁ c₂ => "contradiction: {\n" ++ c₁.toStr ++ "\n}\nand: {\n" ++ c₂.toStr ++ "\n}"    
  | trivial               => "trivial"
  | explode c             => "explode" ++ c.toStr
  | intro c               => "intro\n" ++ c.toStr
  | modusPonens _ c₁ c₂   => "have: {\n" ++ c₁.toStr ++ "\n}\nand: {\n" ++ c₂.toStr ++ "\n}"
  | split c₁ c₂           => "∧ split: {\n" ++ c₁.toStr ++ "\n}\nand: {\n" ++ c₂.toStr ++ "\n}"
  | andLeft _ c           => "∧ left\n" ++ c.toStr
  | andRight _ c          => "∧ right\n" ++ c.toStr
  | orLeft c              => "∨ left\n" ++ c.toStr
  | orRight c             => "∨ right\n" ++ c.toStr
  | cases _ _ c₀ c₁ c₂    => "∨ split: {\n" ++ c₀.toStr ++ "\n}\nor left: {\n" ++ c₁.toStr ++ "\n}\nor right: {\n" ++ c₂.toStr ++ "\n}"
  | generalize c          => "generalize\n" ++ c.toStr
  | specialize _ c        => "specialize\n" ++ c.toStr
  | useInstance _ c       => "use\n" ++ c.toStr
  | exCases _ c₀ c₁       => "∃ cases: {\n" ++ c₀.toStr ++ "\n}\n" ++ c₁.toStr
  | eqRefl                => "refl"
  | eqSymm c              => "symmetry" ++ c.toStr
  | eqTrans _ c₁ c₂       => "trans: {\n" ++ c₁.toStr ++ "\n}\n and: {\n" ++ c₂.toStr ++ "\n}"
  | rewriteEq _ _ c₁ c₂   => "rewrite: {\n" ++ c₁.toStr ++ "\n}\n" ++ c₂.toStr
  | since _               => "since"
  | rwEq _ _ c            => c.toStr   
  | showState c           => c.toStr
  | missing               => "?"
/--/
instance : Repr (DeductionCode L) := ⟨fun b _ => b.toStr L⟩

instance : ToString (DeductionCode L) := ⟨toStr L⟩

variable (dfunc : Q(∀ k, DecidableEq (($L).func k))) (drel : Q(∀ k, DecidableEq (($L).rel k))) (lEq : Q(Language.Eq $L)) 
variable (T : Q(Theory $L)) (eqTh : Q(EqTheory $T))

def display (E : List Q(SyntacticFormula $L)) (e : Q(SyntacticFormula $L)) : MetaM Unit := do
  -- logInfo m!"Language: {L}\nTheory: {T}"
  let (_, m) := E.foldr (fun e (s, m) => (s + 1, m ++ m!"{s+1}:    {e}\n")) (0, m! "")
  logInfo (m ++ m!"⊢\n0:    {e}")

#check Deduction.exCases

def run : (c : DeductionCode L) → (G : List Q(SyntacticFormula $L)) → (e : Q(SyntacticFormula $L)) →
    TermElabM Q($(Qq.toQList (u := u) G) ⟹[$T] $e)
  | assumption,            E, e  => do
    let some eh ← Qq.memQList? (u := u) e E | do display L E e; throwError m!"failed to prove {e} ∈ {E}" --el eVerum
    return DeductionQ.assumptionQ L dfunc drel lEq T (Qq.toQList (u := u) E) e eh
  | trans e₁ c₁ c₂,        E, e₂ => do
    let b₁ ← c₁.run E e₁
    let b₂ ← c₂.run (e₁ :: E) e₂
    return q(Deduction.trans $b₁ $b₂)
  | contradiction e₀ c₁ c₂, E, e₁  => do
    let b₁ ← c₁.run E e₀
    let b₂ ← c₂.run E q(~$e₀)
    return q(Deduction.contradiction $e₁ $b₁ $b₂)
  | trivial,               _, e  => do
    match e with
    | ~q(⊤) => return q(Deduction.trivial)
    | _ => throwError "incorrect structure: {e} should be ⊤"
  | explode c,             E, _  => do
    let b ← c.run E q(⊥)
    return q(Deduction.explode $b)
  | intro c,               E, e  => do
    match e with
    | ~q($e₁ ⟶ $e₂) =>
      let b ← c.run (e₁ :: E) e₂
      return q(Deduction.intro $b)
    | _ => throwError "incorrect structure: {e} should be _ → _"
  | modusPonens e₁ c₁ c₂,  E, e₂ => do
    let b₁ ← c₁.run E q($e₁ ⟶ $e₂)
    let b₂ ← c₂.run E e₁
    return q(Deduction.modusPonens $b₁ $b₂)
  | split c₁ c₂,           E, e  => do
    match e with
    | ~q($e₁ ⋏ $e₂) =>
      let b₁ ← c₁.run E e₁
      let b₂ ← c₂.run E e₂
      return q(Deduction.split $b₁ $b₂)
    | ~q($e₁ ⟷ $e₂) =>
      let b₁ ← c₁.run E q($e₁ ⟶ $e₂)
      let b₂ ← c₂.run E q($e₂ ⟶ $e₁)
      return q(Deduction.splitIff $b₁ $b₂)
    | _ => throwError "incorrect structure: {e} should be _ ⋏ _ or _ ⟷ _"
  | andLeft e₁ c,           E, e₂  => do
      let b ← c.run E q($e₂ ⋏ $e₁)
      return q(Deduction.andLeft $b)
  | andRight e₁ c,           E, e₂  => do
      let b ← c.run E q($e₁ ⋏ $e₂)
      return q(Deduction.andRight $b)
  | orLeft c,               E, e  => do
    match e with
    | ~q($e₁ ⋎ $e₂) =>
      let b ← c.run E e₁
      return q(Deduction.orLeft $b)
    | _ => throwError "incorrect structure: {e} should be _ ⋎ _"
  | orRight c,               E, e  => do
    match e with
    | ~q($e₁ ⋎ $e₂) =>
      let b ← c.run E e₂
      return q(Deduction.orRight $b)
    | _ => throwError "incorrect structure: {e} should be _ ⋎ _"
  | cases e₁ e₂ c₀ c₁ c₂,  E, e  => do
    let b₀ ← c₀.run E q($e₁ ⋎ $e₂)
    let b₁ ← c₁.run (e₁ :: E) e
    let b₂ ← c₂.run (e₂ :: E) e
    return q(Deduction.cases $b₀ $b₁ $b₂)
  | generalize c,          E, e  => do
    match e with
    | ~q(∀' $e) =>
      let ⟨fe, fee⟩ ← SubFormula.Meta.resultFree e
      let ⟨sE, sEe⟩ ← SubFormula.Meta.resultShift₀List E
      let b ← c.run sE fe
      return DeductionQ.generalizeOfEqQ L dfunc drel lEq T
        (Qq.toQList (u := u) E) (Qq.toQList (u := u) sE) e fe sEe fee b
    | _ => throwError "incorrect structure: {e} should be ∀ _"
  | useInstance t c, E, i => do
    match i with
    | ~q(∃' $p) =>
      let ⟨p', pe⟩ ← SubFormula.Meta.resultSubsts (L := L) (k := q(1)) (n := q(0)) q(![$t]) p
      let b ← c.run E p'
      return DeductionQ.useInstanceOfEqQ L dfunc drel lEq T
        (Qq.toQList (u := u) E) t p p' pe b
    | _ => throwError "incorrect structure: {i} should be ∃ _" 
  | exCases e c₀ c₁,          E, i => do
    let ⟨fe, fee⟩ ← SubFormula.Meta.resultFree (L := L) (n := q(0)) e
    let ⟨si, sie⟩ ← SubFormula.Meta.resultShift (L := L) (n := q(0)) i
    let ⟨sE, sEe⟩ ← SubFormula.Meta.resultShift₀List E
    let b₀ ← c₀.run E q(∃' $e)
    let b₁ ← c₁.run (fe :: sE) si
    return DeductionQ.exCasesOfEqQ L dfunc drel lEq T
      (Qq.toQList (u := u) E) (Qq.toQList (u := u) sE) e fe i si sEe fee sie b₀ b₁
  | eqRefl, E, i => do
    match i with
    | ~q(SubFormula.rel Language.Eq.eq ![$i₁, $i₂]) =>
      let ⟨i₁', ie₁⟩ ← SubTerm.Meta.result (L := L) (n := q(0)) SubTerm.Meta.NumeralUnfoldOption.all i₁
      let ⟨i₂', ie₂⟩ ← SubTerm.Meta.result (L := L) (n := q(0)) SubTerm.Meta.NumeralUnfoldOption.all i₂
      if (← isDefEq i₁' i₂') then
        let eqn : Q($i₁' = $i₂') := (q(@rfl (SyntacticTerm $L) $i₁') : Expr)
        let eqn : Q($i₁ = $i₂) := q(Eq.trans $ie₁ $ Eq.trans $eqn $ Eq.symm $ie₂)
        return DeductionQ.eqReflOfEqQ L dfunc drel lEq T (Qq.toQList (u := u) E) i₁ i₂ eqn
      else throwError "term should be equal: {i₁}, {i₂}"
    | ~q($p₁ ⟷ $p₂) =>
      let ⟨p₁', pe₁⟩ ← SubFormula.Meta.result (L := L) (n := q(0)) SubTerm.Meta.NumeralUnfoldOption.all SubFormula.Meta.unfoldAll p₁
      let ⟨p₂', pe₂⟩ ← SubFormula.Meta.result (L := L) (n := q(0)) SubTerm.Meta.NumeralUnfoldOption.all SubFormula.Meta.unfoldAll p₂
      if (← isDefEq p₁' p₂') then
        let eqn : Q($p₁' = $p₂') := (q(@rfl (SyntacticFormula $L) $p₁') : Expr)
        let eqn : Q($p₁ = $p₂) := q(Eq.trans $pe₁ $ Eq.trans $eqn $ Eq.symm $pe₂)
        return DeductionQ.iffReflOfEqQ L dfunc drel lEq T (Qq.toQList (u := u) E) p₁ p₂ eqn
      else throwError "term should be equal: {p₁}, {p₂}"
    | _ => throwError "incorrect structure: {i} should be _ = _ or _ ↔ _"
  | eqSymm c, E, i => do
    match i with
    | ~q(SubFormula.rel Language.Eq.eq ![$i₁, $i₂]) =>
      let b ← c.run E q(“ᵀ!$i₂ = ᵀ!$i₁”)
      return q(Deduction.eqSymm $b)
    | ~q($p ⟷ $q) =>
      let b ← c.run E q($q ⟷ $p)
      return q(Deduction.iffSymm $b)
    | _ => throwError "incorrect structure: {i} should be _ = _ or _ ↔ _"
  | since s, E, e               => do
    Term.elabTerm s (return q($(Qq.toQList (u := u) E) ⟹[$T] $e))
  | showState c,          E, e  => do
    display L E e
    let b ← c.run E e
    return q($b)
  | _, E, e               => do
    display L E e
    throwError m!"proof is missing" 

end DeductionCode

open Lean.Parser

declare_syntax_cat proofElem

@[inline] def proofElemParser (rbp : Nat := 0) : Parser :=
  categoryParser `proofElem rbp

def seqItem      := leading_parser ppLine >> proofElemParser >> Lean.Parser.optional "; "

def seqIndent    := leading_parser many1Indent seqItem

def seq := seqIndent

syntax metaBlock := "by " term

syntax proofBlock := "· " seq

syntax optProofBlock := ("@ " seq)?

syntax (name := notationAssumption) "assumption" : proofElem

syntax (name := notationHave) "have " subformula proofBlock : proofElem

syntax (name := notationContradiction) "contradiction " subformula optProofBlock optProofBlock : proofElem

syntax (name := notationTrivial) "trivial" : proofElem

syntax (name := notationIntro) "intro" : proofElem

syntax (name := notationModusPonens) "suffices" subformula optProofBlock : proofElem

syntax (name := notationSplit)"split" optProofBlock optProofBlock : proofElem

syntax (name := notationAndLeft) "andl" subformula optProofBlock : proofElem

syntax (name := notationAndRight) "andr" subformula optProofBlock : proofElem

syntax (name := notationOrLeft) "left" optProofBlock : proofElem

syntax (name := notationOrRight) "right" optProofBlock : proofElem

syntax (name := notationCases) "cases " subformula " or " subformula optProofBlock proofBlock proofBlock : proofElem

syntax (name := notationGeneralize) "generalize" : proofElem

syntax (name := notationUse) "use " subterm : proofElem

syntax (name := notationExCases) "choose " subformula optProofBlock : proofElem

syntax (name := notationEqRefl) "rfl" : proofElem

syntax (name := notationEqSymm) "symm" : proofElem

syntax (name := notationSince) "since" term : proofElem

syntax (name := notationShowState) "!" : proofElem

syntax (name := notationMissing) "?" : proofElem

private def getSeq (doStx : Syntax) : Syntax :=
  doStx[1]

private def getSeqElems (doSeq : Syntax) : List Syntax :=
  if doSeq.getKind == ``seqIndent then
    doSeq[0].getArgs.toList.map fun arg => arg[0]
  else
    []

def getSeqOfOptProofBlock (proofBlock : Syntax) : Syntax :=
  proofBlock[0][1]

def getSeqOfProofBlock (proofBlock : Syntax) : Syntax :=
  proofBlock[1]

partial def seqToCode (L : Q(Language.{u})) : List Syntax → TermElabM (DeductionCode L)
  | []                => return DeductionCode.missing
  | seqElem::seqElems => do
    let k := seqElem.getKind
    --logInfo f!"k: {k}"
    if k == ``notationAssumption then
      return DeductionCode.assumption
    else if k == ``notationHave then
      let e ← formulaSyntaxToExpr L seqElem[1]
      let c₁ ← seqToCode L (getSeqElems <| getSeqOfProofBlock seqElem[2])
      let c₂ ← seqToCode L seqElems
      return DeductionCode.trans e c₁ c₂
    else if k == ``notationContradiction then
      let s₁ := getSeqOfOptProofBlock seqElem[2] 
      let s₂ := getSeqOfOptProofBlock seqElem[3]
      let e ← formulaSyntaxToExpr L seqElem[1]
      let c₁ := if s₁.isMissing then DeductionCode.assumption else ← seqToCode L (getSeqElems <| s₁)
      let c₂ := if s₂.isMissing then DeductionCode.assumption else ← seqToCode L (getSeqElems <| s₂)
      return DeductionCode.contradiction e c₁ c₂  
    else if k == ``notationTrivial then
      return DeductionCode.trivial
    -- TODO: else if k == ``notationExplode then
    else if k == ``notationIntro then
      --logInfo f!"seqElem : {seqElem}"
      let c ← seqToCode L seqElems
      return DeductionCode.intro c
    else if k == ``notationModusPonens then
      let e ← formulaSyntaxToExpr L seqElem[1]
      let s := getSeqOfOptProofBlock seqElem[2]
      let c₀ := if s.isMissing then DeductionCode.assumption else ← seqToCode L (getSeqElems <| s)
      let c₁ ← seqToCode L seqElems
      return DeductionCode.modusPonens e c₀ c₁
    else if k == ``notationSplit then
      let s₁ := getSeqOfOptProofBlock seqElem[1] 
      let s₂ := getSeqOfOptProofBlock seqElem[2]
      let c₁ := if s₁.isMissing then DeductionCode.assumption else ← seqToCode L (getSeqElems <| s₁)
      let c₂ := if s₂.isMissing then DeductionCode.assumption else ← seqToCode L (getSeqElems <| s₂)
      return DeductionCode.split c₁ c₂
    else if k == ``notationAndLeft then
      let e ← formulaSyntaxToExpr L seqElem[1]
      let s := getSeqOfOptProofBlock seqElem[2] 
      let c := if s.isMissing then DeductionCode.assumption else ← seqToCode L (getSeqElems <| s)
      return DeductionCode.andLeft e c
    else if k == ``notationAndRight then
      let e ← formulaSyntaxToExpr L seqElem[1]
      let s := getSeqOfOptProofBlock seqElem[2] 
      let c := if s.isMissing then DeductionCode.assumption else ← seqToCode L (getSeqElems <| s)
      return DeductionCode.andRight e c
    else if k == ``notationOrLeft then
      let s := getSeqOfOptProofBlock seqElem[1] 
      let c := if s.isMissing then DeductionCode.assumption else ← seqToCode L (getSeqElems <| s)
      return DeductionCode.orLeft c
    else if k == ``notationOrRight then
      let s := getSeqOfOptProofBlock seqElem[1] 
      let c := if s.isMissing then DeductionCode.assumption else ← seqToCode L (getSeqElems <| s)
      return DeductionCode.orRight c
    else if k == ``notationCases then
      let s₀ := getSeqOfOptProofBlock seqElem[4]
      let s₁ := getSeqOfProofBlock seqElem[5]
      let s₂ := getSeqOfProofBlock seqElem[6]
      let e₁ ← formulaSyntaxToExpr L seqElem[1]
      let e₂ ← formulaSyntaxToExpr L seqElem[3]
      let c₀ := if s₀.isMissing then DeductionCode.assumption else ← seqToCode L (getSeqElems <| s₀)
      let c₁ ← seqToCode L (getSeqElems s₁)
      let c₂ ← seqToCode L (getSeqElems s₂)
      return DeductionCode.cases e₁ e₂ c₀ c₁ c₂
    else if k == ``notationGeneralize then
      let c ← seqToCode L seqElems
      return DeductionCode.generalize c
    else if k == ``notationUse then
      let t ← termSyntaxToExpr L seqElem[1]
      let c ← seqToCode L seqElems
      return DeductionCode.useInstance t c
    else if k == ``notationExCases then
      let e ← subFormulaSyntaxToExpr L q(1) seqElem[1]
      let s := getSeqOfOptProofBlock seqElem[2] 
      let c₀ := if s.isMissing then DeductionCode.assumption else ← seqToCode L (getSeqElems <| s)
      let c₁ ← seqToCode L seqElems
      return DeductionCode.exCases e c₀ c₁
    else if k == ``notationEqRefl then
      return DeductionCode.eqRefl
    else if k == ``notationEqSymm then
      let c ← seqToCode L seqElems
      return DeductionCode.eqSymm c
    -- TODO: else if k == ``notationEqTrans then
    -- TODO: else if k == ``notationRewriteEq then
    else if k == ``notationSince then
      return DeductionCode.since seqElem[1]
    else if k == ``notationShowState then
      let c ← seqToCode L seqElems
      return DeductionCode.showState c
    else if k == ``notationMissing then
      return DeductionCode.missing
    else throwError f!"no match: {k}"

syntax (name := elabproof) "proof." seq "□" : term
syntax (name := elabproofShort) "proofBy {" seq "}" : term

open Lean.Parser

#check @Deduction
#check DeductionCode.run

@[term_elab elabproof]
def elabSeq : TermElab := fun stx typ? => do
  let seq := stx[1]
  let some typ := typ? | throwError "error: not a type"
  let some ⟨.succ u, typ'⟩ ← checkSortQ' typ | throwError "error: not a type"
  let ~q(@Deduction $L $dfunc $drel $T $lEq $Γ $p) := typ' | throwError m!"error2: not a type: {typ'}"
  let c ← seqToCode L (getSeqElems seq)
  let E ← Qq.ofQList Γ
  let e ← DeductionCode.run L dfunc drel lEq T c E p
  return e

section
variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)] [L.ORing]
variable {T : Theory L} [EqTheory T]

example : [“0 = &1”] ⟹[T] “⊤ ∧ (2 < 3 → 0 = &1)” :=
  proof.
    split
    @ trivial
    @ intro assumption
  □

example : [“0 = 1”, “0 ≠ 1”] ⟹[T] “⊥” :=
  proof.
    contradiction 0 = 1
  □

example : [“0 = &1”] ⟹[T]
  “⊤ ∧ (2 < 3 → 0 = &1)” :=
  proof.
    have ⊤ · trivial
    split
    @ since
      proof.
        trivial
      □
    @ intro
      assumption
  □

-- generalize
example : [“0 = &1”, “3 < &6 + &7”] ⟹[T] “∀ ∀ ∀ ((#0 = 0 ∨ #1 ≠ 0 ∨ #2 = 0) → ⊤)” :=
  proof.
    generalize 
    generalize 
    generalize
    intro 
    trivial
  □

example :
    [“&0 < 1 → &0 = 0”, “&0 < 1”] ⟹[T] “&0 = 0” :=
  proof.
    suffices &0 < 1
    assumption
  □

example (t : SyntacticSubTerm L 1) :
    [“&0 < 1 → &0 = 0”, “&0 < 1”] ⟹[T] “&0 = 0 ∨ 0 < 2” :=
  proof.
    have &0 = 0
    · suffices &0 < 1
        assumption
    left
  □

example :
    [“∃ #0 < &1”] ⟹[T] “⊤” :=
  proof.
    choose #0 < &1
    trivial
  □


-- rfl
example :
    [] ⟹[T] “2 = 1 + 1” :=
  proof.
    ! symm
    ! rfl
  □

example :
    [] ⟹[T] “2 = 1 + 1 ↔ 1 + 1 = 2” :=
  proof.
    ! symm
    ! rfl
  □

example :
    [“&0 = 0 ∨ ∃ &0 = #0 + 1”] ⟹[T] “⊤” :=
  proof.
    cases &0 = 0 or ∃ &0 = #0 + 1
    · trivial
    · choose &0 = #0 + 1
      trivial
  □

example :
    [] ⟹[T] “∃ ∃ ∃ #0 = #1 + #2” :=
  proof.
    use 1
    use 2
    use 3
    rfl
  □

end

end Meta

end FirstOrder
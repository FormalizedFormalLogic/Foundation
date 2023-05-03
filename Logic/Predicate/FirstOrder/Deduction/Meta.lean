import Logic.Predicate.FirstOrder.Deduction.Deduction
import Logic.Predicate.FirstOrder.Meta

open Qq Lean Elab Meta Tactic Term

namespace FirstOrder

namespace Deduction
open SubFormula
variable {L : Language.{u}} [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)] [L.Eq]
variable {T : Theory L} [EqTheory T]

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

end Deduction

namespace Meta

namespace DeductionQ
open SubFormula
variable (L : Q(Language.{u}))
variable (dfunc : Q(∀ k, DecidableEq (($L).func k))) (drel : Q(∀ k, DecidableEq (($L).rel k))) (lEq : Q(Language.Eq $L)) 
variable (T : Q(Theory $L)) (eqTh : Q(EqTheory $T))

def assumptionQ (Γ : Q(List (SyntacticFormula $L))) (p : Q(SyntacticFormula $L)) (h : Q($p ∈ $Γ)) :
    Q($Γ ⟹[$T] $p) :=
  q(Deduction.assumption $h)

def generalizeOfEqQ (Δ Δ' : Q(List (SyntacticFormula $L))) (p : Q(SyntacticSubFormula $L 1)) (p' : Q(SyntacticFormula $L))
  (hΔ : Q(($Δ).map shift = $Δ')) (hp : Q(free $p = $p')) (b : Q($Δ' ⟹[$T] $p')) : Q($Δ ⟹[$T] ∀' $p) :=
  q(Deduction.generalizeOfEq $hΔ $hp $b)

end DeductionQ

section Syntax
variable (L : Q(Language.{u})) (n : Q(ℕ))
open SubTerm

-- TODO
partial def subTermSyntaxToExpr : Syntax → TermElabM Q(SyntacticSubTerm $L $n)
  | `(subterm| ($s)) => subTermSyntaxToExpr s
  | `(subterm| !$t:term) =>
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
    let et₁ ← subTermSyntaxToExpr t₁
    let et₂ ← subTermSyntaxToExpr t₂
    let (_ : Q(Language.Add $L)) ← synthInstanceQ q(Language.Add $L)
    return q(SubTerm.func Language.Add.add ![$et₁, $et₂])
  | `(subterm| $t₁:subterm * $t₂:subterm) => do
    let et₁ ← subTermSyntaxToExpr t₁
    let et₂ ← subTermSyntaxToExpr t₂
    let (_ : Q(Language.Mul $L)) ← synthInstanceQ q(Language.Mul $L)
    return q(SubTerm.func Language.Mul.mul ![$et₁, $et₂])
  | `(subterm| $t₁:subterm ^ $t₂:subterm) => do
    let et₁ ← subTermSyntaxToExpr t₁
    let et₂ ← subTermSyntaxToExpr t₂
    let (_ : Q(Language.Pow $L)) ← synthInstanceQ q(Language.Pow $L)
    return q(SubTerm.func Language.Pow.pow ![$et₁, $et₂])
  | _                    => throwUnsupportedSyntax
  

-- TODO
partial def subFormulaSyntaxToExpr : (n : Q(ℕ)) → Syntax → TermElabM Q(SyntacticSubFormula $L $n)
  | n, `(subformula| ($p)) => subFormulaSyntaxToExpr n p
  | n, `(subformula| !$t:term)  =>
    Term.elabTerm t (return q(SyntacticSubFormula $L $n))

  | n, `(subformula| $t₁:subterm = $t₂:subterm) => do
    let et₁ ← subTermSyntaxToExpr L n t₁
    let et₂ ← subTermSyntaxToExpr L n t₂
    let (_ : Q(Language.Eq $L)) ← synthInstanceQ q(Language.Eq $L)
    let e : Expr := q(SubFormula.rel Language.Eq.eq ![$et₁, $et₂])
    return e
  | n, `(subformula| $t₁:subterm ≠ $t₂:subterm) => do
    let et₁ ← subTermSyntaxToExpr L n t₁
    let et₂ ← subTermSyntaxToExpr L n t₂
    let (_ : Q(Language.Eq $L)) ← synthInstanceQ q(Language.Eq $L)
    let e : Expr := q(SubFormula.nrel Language.Eq.eq ![$et₁, $et₂])
    return e

  | n, `(subformula| $t₁:subterm < $t₂:subterm) => do
    let et₁ ← subTermSyntaxToExpr L n t₁
    let et₂ ← subTermSyntaxToExpr L n t₂
    let (_ : Q(Language.Lt $L)) ← synthInstanceQ q(Language.Lt $L)
    let e : Expr := q(SubFormula.rel Language.Lt.lt ![$et₁, $et₂])
    return e
  | n, `(subformula| $t₁:subterm ≮ $t₂:subterm) => do
    let et₁ ← subTermSyntaxToExpr L n t₁
    let et₂ ← subTermSyntaxToExpr L n t₂
    let (_ : Q(Language.Lt $L)) ← synthInstanceQ q(Language.Lt $L)
    let e : Expr := q(SubFormula.nrel Language.Lt.lt ![$et₁, $et₂])
    return e

  | _, `(subformula| ⊤)       => return q(⊤)
  | _, `(subformula| ⊥)       => return q(⊥)
  | n, `(subformula| $p ∧ $q) => do
    let ep ← subFormulaSyntaxToExpr n p
    let eq ← subFormulaSyntaxToExpr n q
    let epandeq : Expr := q($ep ⋏ $eq)
    return epandeq
  | n, `(subformula| $p ∨ $q) => do
    let ep ← subFormulaSyntaxToExpr n p
    let eq ← subFormulaSyntaxToExpr n q
    let eporeq : Expr := q($ep ⋏ $eq)
    return eporeq
  | n, `(subformula| ∀ $p)     => do
    let ep ← subFormulaSyntaxToExpr q($n + 1) p
    let allep : Expr := q(∀' $ep)
    return allep
  | n, `(subformula| ∃ $p)     => do
    let ep ← subFormulaSyntaxToExpr q($n + 1) p
    let exep : Expr := q(∃' $ep)
    return exep

  | n, `(subformula| ¬$p)     => do
    let ep ← subFormulaSyntaxToExpr n p
    have nep : Expr := q(~$ep)
    return nep
  | n, `(subformula| $p → $q) => do
    let ep ← subFormulaSyntaxToExpr n p
    let eq ← subFormulaSyntaxToExpr n q
    let eptoeq : Expr := q($ep ⟶ $eq)
    return eptoeq
  | n, `(subformula| $p ↔ $q) => do
    let ep ← subFormulaSyntaxToExpr n p
    let eq ← subFormulaSyntaxToExpr n q
    let epiffeq : Expr := q($ep ⟷ $eq)
    return epiffeq  
  | _, _                   => throwUnsupportedSyntax

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
  | modusPonens           : Q(SyntacticFormula $L) → DeductionCode L → DeductionCode L → DeductionCode L  
  | split         : DeductionCode L → DeductionCode L → DeductionCode L
  -- TODO
  | cases         : (e₁ e₂ : Q(SyntacticFormula $L)) → DeductionCode L → DeductionCode L → DeductionCode L → DeductionCode L
  | generalize    : DeductionCode L → DeductionCode L
  -- TODO
  | exCases       : Q(SyntacticFormula $L) → DeductionCode L → DeductionCode L → DeductionCode L
  | eqRefl        : DeductionCode L
  | eqSymm        : DeductionCode L → DeductionCode L
  | eqTrans       : Q(SyntacticFormula $L) → DeductionCode L → DeductionCode L → DeductionCode L
  | rewriteEq     : (e₁ e₂ : Q(SyntacticTerm $L)) → DeductionCode L → DeductionCode L → DeductionCode L
  | since         : Syntax → DeductionCode L
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
  | cases _ _ c₀ c₁ c₂    => "∨ split: {\n" ++ c₀.toStr ++ "\n}\nor left: {\n" ++ c₁.toStr ++ "\n}\nor right: {\n" ++ c₂.toStr ++ "\n}"
  | generalize c          => "generalize\n" ++ c.toStr
  | exCases _ c₀ c₁       => "∃ cases: {\n" ++ c₀.toStr ++ "\n}\n" ++ c₁.toStr
  | eqRefl                => "refl"
  | eqSymm c              => "symmetry" ++ c.toStr
  | eqTrans _ c₁ c₂       => "trans: {\n" ++ c₁.toStr ++ "\n}\n and: {\n" ++ c₂.toStr ++ "\n}"
  | rewriteEq _ _ c₁ c₂   => "rewrite: {\n" ++ c₁.toStr ++ "\n}\n" ++ c₂.toStr
  | since _               => "since"
  | missing               => "?"

instance : Repr (DeductionCode L) := ⟨fun b _ => b.toStr L⟩

instance : ToString (DeductionCode L) := ⟨toStr L⟩

variable (dfunc : Q(∀ k, DecidableEq (($L).func k))) (drel : Q(∀ k, DecidableEq (($L).rel k))) (lEq : Q(Language.Eq $L)) 
variable (T : Q(Theory $L)) (eqTh : Q(EqTheory $T))

def run : (c : DeductionCode L) → (G : List Q(SyntacticFormula $L)) → (e : Q(SyntacticFormula $L)) →
    TermElabM Q($(Qq.toQList (u := u) G) ⟹[$T] $e)
  | assumption,            E, e  => do
    let some eh ← Qq.memQList? (u := u) e E | throwError m!"failed to prove {e} ∈ {E}" --el eVerum
    return DeductionQ.assumptionQ L dfunc drel lEq T (Qq.toQList (u := u) E) e eh
  | trans e₁ c₁ c₂,        E, e₂ => do
    let b₁ ← c₁.run E e₁
    let b₂ ← c₂.run (e₁ :: E) e₂
    return q(Deduction.trans $b₁ $b₂)
  | contradiction e c₁ c₂, E, _  => do
    let b₁ ← c₁.run E e
    let b₂ ← c₂.run E q(~$e)
    return q(Deduction.contradiction $e $b₁ $b₂)
  | trivial,               _, e  => do
    match e with
    | ~q(⊤) => return q(Deduction.trivial)
    | _ => throwError "incorrect structure"
  | explode c,             E, _  => do
    let b ← c.run E q(⊥)
    return q(Deduction.explode $b)
  | intro c,               E, e  => do
    match e with
    | ~q($e₁ ⟶ $e₂) =>
      let b ← c.run (e₁ :: E) e₂
      return q(Deduction.intro $b)
    | _ => throwError "incorrect structure"
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
    | _ => throwError "incorrect structure"
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
    | _ => throwError "incorrect structure: generalize"
  | since s, E, e               => do
    Term.elabTerm s (return q($(Qq.toQList (u := u) E) ⟹[$T] $e))
  | _, E, e               => do
    throwError m!"proof is missing:\n  {E}\n  ⊢\n  {e}"

elab "test" : term => do
  have L : Q(Language.{0}) := q(Language.oring)
  let c : DeductionCode L := intro (trans q(⊤) trivial assumption)
  let dfunc ← synthInstanceQ q(∀ k, DecidableEq (($L).func k))
  let drel  ← synthInstanceQ q(∀ k, DecidableEq (($L).rel k))
  let lEq : Q(Language.Eq $L)   ← synthInstanceQ q(Language.Eq $L)
  let T := q(@Theory.Eq $L $lEq)
  let b ← c.run L dfunc drel lEq T [q(⊥)] q(⊤ ⟶ ⊤)
  logInfo m! "{b}"
  return b

#eval test

end DeductionCode


open Lean.Parser

declare_syntax_cat proofElem

@[inline] def proofElemParser (rbp : Nat := 0) : Parser :=
  categoryParser `proofElem rbp

def seqItem      := leading_parser ppLine >> proofElemParser >> Lean.Parser.optional "; "

def seqIndent    := leading_parser many1Indent seqItem

def seq := seqIndent

syntax proofBlock := "· " seq
syntax optProofBlock := ("@ " seq)?

syntax (name := notationAssumption) "assumption" : proofElem

syntax (name := notationHave) "have " subformula proofBlock : proofElem

syntax (name := notationContradiction) "contradiction " subformula optProofBlock optProofBlock : proofElem

syntax (name := notationTrivial) "trivial" : proofElem

syntax (name := notationIntro) "intro" : proofElem

syntax (name := notationSplit)"split" optProofBlock optProofBlock : proofElem

syntax (name := notationCases) "cases " subformula " or " subformula optProofBlock proofBlock proofBlock : proofElem

syntax (name := notationGeneralize) "generalize" : proofElem

syntax (name := notationSince) "since" term : proofElem


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
    -- TODO: else if k == ``notationModusPonens then
    else if k == ``notationSplit then
      let s₁ := getSeqOfOptProofBlock seqElem[1] 
      let s₂ := getSeqOfOptProofBlock seqElem[2]
      let c₁ := if s₁.isMissing then DeductionCode.assumption else ← seqToCode L (getSeqElems <| s₁)
      let c₂ := if s₂.isMissing then DeductionCode.assumption else ← seqToCode L (getSeqElems <| s₂)
      return DeductionCode.split c₁ c₂
    else if k == ``notationCases then
      let s₀ := getSeqOfOptProofBlock seqElem[4] 
      let s₁ := getSeqOfOptProofBlock seqElem[5]
      let s₂ := getSeqOfOptProofBlock seqElem[6]
      let e₁ ← formulaSyntaxToExpr L seqElem[1]
      let e₂ ← formulaSyntaxToExpr L seqElem[3]
      let c₀ := if s₀.isMissing then DeductionCode.assumption else ← seqToCode L (getSeqElems <| s₀)
      let c₁ ← seqToCode L (getSeqElems s₁)
      let c₂ ← seqToCode L (getSeqElems s₂)
      return DeductionCode.cases e₁ e₂ c₀ c₁ c₂
    else if k == ``notationGeneralize then
      let c ← seqToCode L seqElems
      return DeductionCode.generalize c
      
    -- TODO: else if k == ``notationExCases then
    -- TODO: else if k == ``notationEqRefl then
    -- TODO: else if k == ``notationEqSymm then
    -- TODO: else if k == ``notationEqTrans then
    -- TODO: else if k == ``notationRewriteEq then
    else if k == ``notationSince then
      return DeductionCode.since seqElem[1]
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
 
example : [“0 = &1”] ⟹[T] “⊤ ∧ (2 < 3 → 0 = &1)” :=
  proof.
    have ⊤
    · trivial
    split
    @ since
      proof.
        trivial
      □
    @ intro
      assumption
  □

-- generalize
example : [“0 = &1”] ⟹[T] “∀ ∀ ∀ ((#0 = 0 ∨ #1 ≠ 0 ∨ #2 = 0) → ⊤)” :=
  proof.
    generalize
    generalize
    generalize
    intro
    trivial
  □
end

end Meta

end FirstOrder
import Logic.Propositional.Basic.Calculus
import Logic.Vorspiel.Meta

open Qq Lean Elab Meta Tactic

namespace LO

inductive Litform (α : Type*) : Type _
  | atom (a : α)  : Litform α
  | verum         : Litform α
  | falsum        : Litform α
  | and           : Litform α → Litform α → Litform α
  | or            : Litform α → Litform α → Litform α
  | neg           : Litform α → Litform α
  | imply         : Litform α → Litform α → Litform α

namespace Litform

instance : LogicSymbol (Litform α) where
  top   := Litform.verum
  bot   := Litform.falsum
  wedge := Litform.and
  vee   := Litform.or
  tilde := Litform.neg
  arrow := Litform.imply

namespace Meta

variable (F : Q(Type*)) (ls : Q(LogicSymbol $F))

abbrev Lit (F : Q(Type*)) := Litform Q($F)

abbrev toExpr : Lit F → Q($F)
  | atom e  => q($e)
  | ⊤       => q(⊤)
  | ⊥       => q(⊥)
  | p ⋏ q   => q($(toExpr p) ⋏ $(toExpr q))
  | p ⋎ q   => q($(toExpr p) ⋎ $(toExpr q))
  | ~p      => q(~$(toExpr p))
  | p ⟶ q  => q($(toExpr p) ⟶ $(toExpr q))

partial def denote : Q($F) → MetaM (Lit F)
  | ~q(⊤)        => return ⊤
  | ~q(⊥)        => return ⊥
  | ~q($p ⋏ $q)  => return (←denote p) ⋏ (←denote q)
  | ~q($p ⋎ $q)  => return (←denote p) ⋎ (←denote q)
  | ~q($p ⟶ $q) => return (←denote p) ⟶ (←denote q)
  | ~q($p ⟷ $q)  => return (←denote p) ⟷ (←denote q)
  | ~q(~$p)      => return ~(←denote p)
  | ~q($e)       => return atom e

instance denotation : Denotation q($F) (Lit F) where
  denote' := denote F ls
  toExpr' := toExpr F ls

abbrev DEq (p q : Lit F) :=
  letI := denotation F ls
  Denotation.DEq F p q

end Meta

end Litform

class DeMorgan (F : Type*) [LogicSymbol F] where
  verum           : ~(⊤ : F) = ⊥
  falsum          : ~(⊥ : F) = ⊤
  imply (p q : F) : (p ⟶ q) = ~p ⋎ q
  and (p q : F)   : ~(p ⋏ q) = ~p ⋎ ~q
  or (p q : F)    : ~(p ⋎ q) = ~p ⋏ ~q
  neg (p : F)     : ~~p = p

class OneSided (F : Type*) [LogicSymbol F] where
  Derivation : List F → Type
  verum (Δ : List F) : Derivation (⊤ :: Δ)
  and {p q : F} {Δ : List F} : Derivation (p :: Δ) → Derivation (q :: Δ) → Derivation (p ⋏ q :: Δ)
  or {p q : F} {Δ : List F} : Derivation (p :: q :: Δ) → Derivation (p ⋎ q :: Δ)
  wk {Δ Γ : List F} : Derivation Δ → Δ ⊆ Γ → Derivation Γ
  em {p} {Δ : List F} (hp : ~p ∈ Δ) : Derivation (p :: Δ)

class RawfulOneSided (F : Type*) [LogicSymbol F] [System F] extends OneSided F where
  toProof (T : Set F) (p : F) : Derivation [p] → T ⊢ p

namespace OneSided

variable {F : Type*} [LogicSymbol F] [OneSided F]

scoped prefix:45 "⊢ᴸ " => Derivation

variable {Δ : List F} {p q r : F}

def rotate (d : ⊢ᴸ Δ ++ [p]) : ⊢ᴸ (p :: Δ) := wk d (by simp)

def tail (d : ⊢ᴸ Δ) : ⊢ᴸ (p :: Δ) := wk d (by simp)

def rOr (d : ⊢ᴸ Δ ++ [p, q]) : ⊢ᴸ p ⋎ q :: Δ :=
  or (wk d $ by simpa using List.subset_cons_of_subset p (List.subset_cons q Δ))

def rAnd (dp : ⊢ᴸ Δ ++ [p]) (dq : ⊢ᴸ Δ ++ [q]) : ⊢ᴸ p ⋏ q :: Δ := and (wk dp $ by simp) (wk dq $ by simp)

def emOfEq (hp : ~p = q) (h : q ∈ Δ) : ⊢ᴸ p :: Δ := em (by simpa[hp])

end OneSided

namespace TaitStyle
open Propositional

section lemmas

variable {F : Type*} [LogicSymbol F] [DeMorgan F]

lemma neg_or_eq_of_eq {p q p' q' : F} (hp : ~p = p') (hq : ~q = q') :
    ~(p ⋎ q) = p' ⋏ q' := by simp[DeMorgan.or, hp, hq]

lemma neg_and_eq_of_eq {p q p' q' : F} (hp : ~p = p') (hq : ~q = q') :
    ~(p ⋏ q) = p' ⋎ q' := by simp[DeMorgan.and, hp, hq]

lemma imp_eq {p q p' : F} (hp : ~p = p') :
    p ⟶ q = p' ⋎ q := by simp[DeMorgan.imply, hp]

end lemmas

variable (F : Q(Type*)) (ls : Q(LogicSymbol $F)) (dm : Q(DeMorgan $F))
open Propositional

abbrev Lit (F : Q(Type*)) := Formula Q($F)

namespace Lit

def ofLitform : Litform.Meta.Lit F → Lit F
  | Litform.atom e => Formula.atom e
  | ⊤              => ⊤
  | ⊥              => ⊥
  | ~p             => ~ofLitform p
  | p ⋏ q          => ofLitform p ⋏ ofLitform q
  | p ⋎ q          => ofLitform p ⋎ ofLitform q
  | p ⟶ q         => ofLitform p ⟶ ofLitform q

def toLitform : Lit F → Litform.Meta.Lit F
  | Formula.atom e  => Litform.atom e
  | Formula.natom e => ~Litform.atom e
  | ⊤               => ⊤
  | ⊥               => ⊥
  | p ⋏ q           => toLitform p ⋏ toLitform q
  | p ⋎ q           => toLitform p ⋎ toLitform q

instance denotation : Denotation q($F) (Lit F) where
  denote' := fun e => return ofLitform F (←Litform.Meta.denote F ls e)
  toExpr' := fun p => Litform.Meta.toExpr F ls (toLitform F p)

local notation:50 p " ≡ᴸ " q => Litform.Meta.DEq F ls p q

local notation "toExprᴸ" => Litform.Meta.toExpr F ls

abbrev toExpr (p : Lit F) := letI := denotation F ls; Denotation.toExpr F p

local notation "toExpr" => toExpr F ls

abbrev DEq (p q : Lit F) :=
  letI := denotation F ls
  Denotation.DEq F p q

def negToExprEqToExprNeg' : (p : Lit F) → Q(~$(toExpr p) = $(toExpr (Formula.neg p)))
  | Formula.atom _  => q(rfl)
  | Formula.natom e => q(DeMorgan.neg $e)
  | ⊤               => q(DeMorgan.verum)
  | ⊥               => q(DeMorgan.falsum)
  | p ⋏ q           => letI := Litform.Meta.denotation F ls;
    let ep := toExpr p
    let enp := toExpr (Formula.neg p)
    let eq := toExpr q
    let enq := toExpr (Formula.neg q)
    have hp : Q(~$ep = $enp) := q($(negToExprEqToExprNeg' p))
    have hq : Q(~$eq = $enq) := q($(negToExprEqToExprNeg' q))
    q(neg_and_eq_of_eq $hp $hq)
  | p ⋎ q           => letI := Litform.Meta.denotation F ls;
    let ep := toExpr p
    let enp := toExpr (Formula.neg p)
    let eq := toExpr q
    let enq := toExpr (Formula.neg q)
    have hp : Q(~$ep = $enp) := q($(negToExprEqToExprNeg' p))
    have hq : Q(~$eq = $enq) := q($(negToExprEqToExprNeg' q))
    q(neg_or_eq_of_eq $hp $hq)

def negToExprEqToExprNeg (p : Lit F) : Q(~$(toExpr p) = $(toExpr (~p))) :=
  negToExprEqToExprNeg' F ls dm p

def implyToExprEqToExprImply (p q : Lit F) : Q($(toExpr p) ⟶ $(toExpr q) = $(toExpr (p ⟶ q))) := by
  let ep := toExpr p
  let enp := toExpr (Formula.neg p)
  have hp : Q(~$ep = $enp) := q($(negToExprEqToExprNeg' F ls dm p))
  exact q(imp_eq $hp)

def toLitformOfLitform : (p : Litform.Meta.Lit F) → p ≡ᴸ (toLitform F (ofLitform F p))
  | Litform.atom e => letI := Litform.Meta.denotation F ls; Denotation.DEq.refl _
  | ⊤              => letI := Litform.Meta.denotation F ls; Denotation.DEq.refl _
  | ⊥              => letI := Litform.Meta.denotation F ls; Denotation.DEq.refl _
  | p ⋏ q          => letI := Litform.Meta.denotation F ls; ⟨
    let ep := toExprᴸ p
    let ep' := toExprᴸ (toLitform F (ofLitform F p))
    let eq := toExprᴸ q
    let eq' := toExprᴸ (toLitform F (ofLitform F q))
    have hp : Q($ep = $ep') := q($((toLitformOfLitform p).expr))
    have hq : Q($eq = $eq') := q($((toLitformOfLitform q).expr))
    q(congr_arg₂ _ $hp $hq)⟩
  | p ⋎ q          => letI := Litform.Meta.denotation F ls; ⟨
    let ep := toExprᴸ p
    let ep' := toExprᴸ (toLitform F (ofLitform F p))
    let eq := toExprᴸ q
    let eq' := toExprᴸ (toLitform F (ofLitform F q))
    have hp : Q($ep = $ep') := q($((toLitformOfLitform p).expr))
    have hq : Q($eq = $eq') := q($((toLitformOfLitform q).expr))
    q(congr_arg₂ _ $hp $hq)⟩
  | ~p             => letI := Litform.Meta.denotation F ls; ⟨
    let ep := toExprᴸ p
    let ep' := toExprᴸ (toLitform F (ofLitform F p))
    let enp' := toExprᴸ (toLitform F (~ofLitform F p))
    have hp : Q($ep = $ep') := q($((toLitformOfLitform p).expr))
    have hnp : Q(~$ep' = $enp') := q($(negToExprEqToExprNeg F ls dm (ofLitform F p)))
    by simp[ofLitform, toLitform]
       exact q(Eq.trans (congr_arg _ $hp) $hnp)⟩
  | p ⟶ q          => letI := Litform.Meta.denotation F ls; ⟨
    let ep := toExprᴸ p
    let ep' := toExprᴸ (toLitform F (ofLitform F p))
    let eq := toExprᴸ q
    let eq' := toExprᴸ (toLitform F (ofLitform F q))
    let enpq := toExprᴸ (toLitform F (ofLitform F p ⟶ ofLitform F q))
    have hp : Q($ep = $ep') := q($((toLitformOfLitform p).expr))
    have hq : Q($eq = $eq') := q($((toLitformOfLitform q).expr))
    have hpq : Q($ep' ⟶ $eq' = $enpq) := q($(implyToExprEqToExprImply F ls dm (ofLitform F p) (ofLitform F q)))
    q(Eq.trans (congr_arg₂ _ $hp $hq) $hpq)⟩

end Lit

set_option linter.unusedVariables false in
abbrev DerivationQ {F : Q(Type*)} (ls : Q(LogicSymbol $F)) (os : Q(OneSided $F)) (G : List (Lit F)) :=
  Q(OneSided.Derivation $(Denotation.toExprₗ (Lit.denotation F ls) G))

namespace DerivationQ
open Denotation

variable {F : Q(Type*)} {ls : Q(LogicSymbol $F)} {os : Q(OneSided $F)} (G : List (Lit F))

abbrev DEqFun {F : Q(Type*)} (ls : outParam (Q(LogicSymbol $F))) (f : Q($F → $F)) (p q : Lit F) :=
  letI := Lit.denotation F ls
  Denotation.DEqFun f p q

def DEq {F : Q(Type*)} : Lit F → Lit F → MetaM Bool
  | Formula.atom e,  Formula.atom e'  => Lean.Meta.isDefEq e e'
  | Formula.natom e, Formula.natom e' => Lean.Meta.isDefEq e e'
  | ⊤,               ⊤                => return true
  | ⊥,               ⊥                => return true
  | p ⋏ q,           p' ⋏ q'          => return (← DEq p p') && (← DEq q q')
  | p ⋎ q,           p' ⋎ q'          => return (← DEq p p') && (← DEq q q')
  | _,               _                => return false

def DMem {F : Q(Type*)} (p : Lit F) (Δ : List (Lit F)) : MetaM Bool :=
  Δ.foldrM (fun q ih => return (←DEq p q) || ih) false

def rotate {p : Lit F} (d : DerivationQ ls os (G ++ [p])) : DerivationQ ls os (p :: G) :=
  letI := Lit.denotation F ls
  let x : Q(OneSided.Derivation ($(Denotation.toExprₗ (Lit.denotation F ls) G) ++ [$(toExpr F p)])) := d
  q(OneSided.rotate $x)

def tail {p : Lit F} (d : DerivationQ ls os G) : DerivationQ ls os (p :: G) :=
  letI := Lit.denotation F ls
  q(OneSided.tail $d)

def verum : DerivationQ ls os (⊤ :: G) := q(OneSided.verum _)

def emOfEq (dm : Q(DeMorgan $F)) {p : Lit F} (G) : MetaM (DerivationQ ls os (p :: G)) :=
  letI := Lit.denotation F ls
  do let some h ← Denotation.memList? (Lit.denotation F ls) (~p) G | throwError m! "failed to prove {~p} ∈ {G}"
     let e : Q(~$(toExpr F p) = $(toExpr F $ ~p)) := q($(Lit.negToExprEqToExprNeg F ls dm p))
     return q(OneSided.emOfEq $e $h)

def rOr {p q : Lit F} (d : DerivationQ ls os (G ++ [p, q])) : DerivationQ ls os (p ⋎ q :: G) :=
  letI := Lit.denotation F ls
  let x : Q(OneSided.Derivation ($(Denotation.toExprₗ (Lit.denotation F ls) G) ++ [$(toExpr F p), $(toExpr F q)])) := d
  q(OneSided.rOr $x)

def rAnd {p q : Lit F} (dp : DerivationQ ls os (G ++ [p])) (dq : DerivationQ ls os (G ++ [q])) :
    DerivationQ ls os (p ⋏ q :: G) :=
  letI := Lit.denotation F ls
  let xp : Q(OneSided.Derivation ($(Denotation.toExprₗ (Lit.denotation F ls) G) ++ [$(toExpr F p)])) := dp
  let xq : Q(OneSided.Derivation ($(Denotation.toExprₗ (Lit.denotation F ls) G) ++ [$(toExpr F q)])) := dq
  q(OneSided.rAnd $xp $xq)

def prove {F : Q(Type*)} (ls : Q(LogicSymbol $F)) (dm : Q(DeMorgan $F)) (os : Q(OneSided $F)) :
    ℕ → (G : List (Lit F)) → MetaM (DerivationQ ls os G)
  | 0,     _      => throwError "failed!"
  | _,     []     => throwError "empty goal"
  | s + 1, p :: G => do
    -- proof search
    if (←DMem (~p) G) then
      emOfEq dm G
    else
    match p with
    | ⊤               => pure $ verum G
    | ⊥               => do
      let d ← prove ls dm os s G
      return tail G d
    | p ⋎ q           => do
      let d ← prove ls dm os s (G ++ [p, q])
      return rOr G d
    | p ⋏ q           => do
      let dp ← prove ls dm os s (G ++ [p])
      let dq ← prove ls dm os s (G ++ [q])
      return rAnd G dp dq
    | Formula.atom a  => do
      let d ← prove ls dm os s (G ++ [Formula.atom a])
      return rotate G d
    | Formula.natom a => do
      let d ← prove ls dm os s (G ++ [Formula.natom a])
      return rotate G d

end DerivationQ

end TaitStyle

end LO

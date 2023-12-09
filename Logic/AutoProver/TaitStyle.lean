import Logic.Propositional.Basic.Calculus
import Logic.AutoProver.Litform
import Logic.Vorspiel.Meta

open Qq Lean Elab Meta Tactic

namespace LO

namespace OneSided

variable {F : Type*} [LogicSymbol F] [OneSided F]

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
abbrev DerivationQ {F : Q(Type u)} (ls : Q(LogicSymbol $F)) (os : Q(OneSided.{u,v} $F)) (G : List (Lit F)) :=
  Q(OneSided.Derivation $(Denotation.toExprₗ (Lit.denotation F ls) G))

namespace DerivationQ
open Denotation

variable {F : Q(Type u)} {ls : Q(LogicSymbol $F)} {os : Q(OneSided.{u, v} $F)} (G : List (Lit F))

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
  do let some h ← Denotation.memList? (Lit.denotation F ls) (~p) G | throwError m! "failed to derive {~p} ∈ {G}"
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

def derive {F : Q(Type u)} (ls : Q(LogicSymbol $F)) (dm : Q(DeMorgan $F)) (os : Q(OneSided.{u, v} $F)) :
    ℕ → (G : List (Lit F)) → MetaM (DerivationQ ls os G)
  | 0,     G      => throwError f!"failed! {G}"
  | _,     []     => throwError "empty goal"
  | s + 1, p :: G => do
    -- proof search
    if (←DMem (~p) G) then
      emOfEq dm G
    else
    match p with
    | ⊤               => pure $ verum G
    | ⊥               => do
      let d ← derive ls dm os s G
      return tail G d
    | p ⋎ q           => do
      let d ← derive ls dm os s (G ++ [p, q])
      return rOr G d
    | p ⋏ q           => do
      let dp ← derive ls dm os s (G ++ [p])
      let dq ← derive ls dm os s (G ++ [q])
      return rAnd G dp dq
    | Formula.atom a  => do
      let d ← derive ls dm os s (G ++ [Formula.atom a])
      return rotate G d
    | Formula.natom a => do
      let d ← derive ls dm os s (G ++ [Formula.natom a])
      return rotate G d

end DerivationQ

open Lit

def prove {F : Q(Type u)}
    (ls : Q(LogicSymbol $F)) (dm : Q(DeMorgan $F))
    (sys : Q(System $F)) (_ : Q(LawfulOneSided.{u, v} $F))
    (s : ℕ) (T : Q(Set $F)) (p : Q($F)) : MetaM Q($T ⊢ $p) :=
  letI := Litform.Meta.denotation F ls; do
  let lf : Litform.Meta.Lit F ← Denotation.denote F p
  let l := ofLitform F lf
  let p' := Denotation.toExpr F (toLitform F l)
  let eq : Q($p = $p') := (toLitformOfLitform F ls dm lf).expr
  let d' : Q(⊢ᴸ [$p']) ← DerivationQ.derive ls dm q(LawfulOneSided.toOneSided) s [l]
  let b : Q($T ⊢ $p) := q(LawfulOneSided.toProof (Eq.symm $eq ▸ $d') $T)
  return b

elab "tryProve" n:(num)? : tactic => do
  let s : ℕ :=
    match n with
    | some n => n.getNat
    | none   => 16
  let goalType ← Elab.Tactic.getMainTarget
  let some ⟨.succ u, ty⟩ ← checkSortQ' goalType | throwError "error: not a type"
  let ~q(@HasTurnstile.turnstile.{u} $F _ $ss $T $p) := ty | throwError "error: not a type 2"
  let .some instLS ← trySynthInstanceQ (q(LogicSymbol.{u} $F) : Q(Type u))
    | throwError m! "error: failed to find instance LogicSymbol {F}"
  let .some instDM ← trySynthInstanceQ q(DeMorgan $F)
    | throwError m! "error: failed to find instance DeMorgan {F}"
  let .some instSys ← trySynthInstanceQ q(System $F)
    | throwError m! "error: failed to find instance System {F}"
  let .some instLOS ← trySynthInstanceQ q(LawfulOneSided.{u, u} $F)
    | throwError m! "error: failed to find instance LawfulOneSided {F}"
  let b ← prove instLS instDM instSys instLOS s T p
  Lean.Elab.Tactic.closeMainGoal b

def prove! {F : Q(Type u)}
    (ls : Q(LogicSymbol $F)) (dm : Q(DeMorgan $F))
    (sys : Q(System $F)) (_ : Q(LawfulOneSided.{u, v} $F))
    (s : ℕ) (T : Q(Set $F)) (p : Q($F)) : MetaM Q($T ⊢! $p) :=
  letI := Litform.Meta.denotation F ls; do
  let lf : Litform.Meta.Lit F ← Denotation.denote F p
  let l := ofLitform F lf
  let p' := Denotation.toExpr F (toLitform F l)
  let eq : Q($p = $p') := (toLitformOfLitform F ls dm lf).expr
  let d' : Q(⊢ᴸ [$p']) ← DerivationQ.derive ls dm q(LawfulOneSided.toOneSided) s [l]
  let b : Q($T ⊢! $p) := q(⟨LawfulOneSided.toProof (Eq.symm $eq ▸ $d') $T⟩)
  return b

#check @System.Provable

elab "try_prove" n:(num)? : tactic => do
  let s : ℕ :=
    match n with
    | some n => n.getNat
    | none   => 16
  let goalType ← Elab.Tactic.getMainTarget
  let ty ← inferPropQ goalType
  let ~q(@System.Provable $F $j $jj $T $p) := ty | throwError "error: not a type 2"
  let .some instLS ← trySynthInstanceQ (q(LogicSymbol $F) : Q(Type u_2))
    | throwError m! "error: failed to find instance LogicSymbol {F}"
  let .some instDM ← trySynthInstanceQ q(DeMorgan $F)
    | throwError m! "error: failed to find instance DeMorgan {F}"
  let .some instSys ← trySynthInstanceQ q(System $F)
    | throwError m! "error: failed to find instance System {F}"
  let .some instLOS ← trySynthInstanceQ q(LawfulOneSided.{u_2,u_2} $F)
    | throwError m! "error: failed to find instance LawfulOneSided {F}"
  let b ← prove! instLS instDM instSys instLOS s T p
  Lean.Elab.Tactic.closeMainGoal b

section test

variable (T : Theory ℕ) (p : Formula ℕ)

example : T ⊢ p ⟶ p := by tryProve

example : T ⊢ p ⟶ p ⋎ q := by tryProve

example : T ⊢ q ⋎ p ⟷ p ⋎ q := by tryProve 5

example : T ⊢! p ⋎ q ⋎ r ⋎ s ⟷ r ⋎ s ⋎ q ⋎ p := by try_prove

example : T ⊢! p ⟷ p ⋎ p ⋎ p ⋎ p ⋎ p ⋎ p ⋎ p := by try_prove

example : T ⊢! ((p ⟶ q) ⟶ p) ⟶ p := by try_prove

example : T ⊢! (p ⟶ q) ⋎ (q ⟶ p) := by try_prove

end test

end TaitStyle

end LO

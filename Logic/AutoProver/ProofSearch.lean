import Logic.Propositional.Basic.Calculus
import Logic.AutoProver.Litform
import Logic.Vorspiel.Meta

namespace LO

namespace Gentzen

variable {F : Type*} [LogicSymbol F] [Gentzen F]

variable {Γ Δ : List F} {p q r : F}

def rotateLeft (d : Γ ++ [p] ⊢ᴳ Δ) : p :: Γ ⊢ᴳ Δ := wk d (by simp) (by simp)

def rotateRight (d : Γ ⊢ᴳ Δ ++ [p]) : Γ ⊢ᴳ p :: Δ := wk d (by simp) (by simp)

def rEmLeft (h : p ∈ Δ) : p :: Γ ⊢ᴳ Δ := em (by simp) h

def rEmRight (h : p ∈ Γ) : Γ ⊢ᴳ p :: Δ := em h (by simp)

def rNegLeft (dp : Γ ⊢ᴳ Δ ++ [p]) : ~p :: Γ ⊢ᴳ Δ :=
  negLeft (wk dp (by simp) (by simp))

def rNegRight (dp : Γ ++ [p] ⊢ᴳ Δ) : Γ ⊢ᴳ ~p :: Δ :=
  negRight (wk dp (by simp) (by simp))

def rOrLeft (dp : Γ ++ [p] ⊢ᴳ Δ) (dq : Γ ++ [q] ⊢ᴳ Δ) : p ⋎ q :: Γ ⊢ᴳ Δ :=
  orLeft (wk dp (by simp) (by simp)) (wk dq (by simp) (by simp))

def rOrRight (d : Γ ⊢ᴳ Δ ++ [p, q]) : Γ ⊢ᴳ p ⋎ q :: Δ :=
  orRight (wk d (by simp) $ by simpa using List.subset_cons_of_subset p (List.subset_cons q Δ))

def rAndLeft (d : Γ ++ [p, q] ⊢ᴳ Δ) : p ⋏ q :: Γ ⊢ᴳ Δ :=
  andLeft (wk d (by simpa using List.subset_cons_of_subset p (List.subset_cons q Γ)) (by simp))

def rAndRight (dp : Γ ⊢ᴳ Δ ++ [p]) (dq : Γ ⊢ᴳ Δ ++ [q]) : Γ ⊢ᴳ p ⋏ q :: Δ :=
  andRight (wk dp (by simp) (by simp)) (wk dq (by simp) (by simp))

def rImplyLeft (dp : Γ ⊢ᴳ Δ ++ [p]) (dq : Γ ++ [q] ⊢ᴳ Δ) : (p ⟶ q) :: Γ ⊢ᴳ Δ :=
  implyLeft (wk dp (by simp) (by simp)) (wk dq (by simp) (by simp))

def rImplyRight (d : Γ ++ [p] ⊢ᴳ Δ ++ [q]) : Γ ⊢ᴳ (p ⟶ q) :: Δ :=
  implyRight (wk d (by simp) (by simp))

end Gentzen

namespace AutoProver
open Qq Lean Elab Meta Tactic Litform Litform.Meta

#check TwoSided.Derivation

set_option linter.unusedVariables false in
abbrev DerivationQ {F : Q(Type u)} (ls : Q(LogicSymbol $F)) (gz : Q(Gentzen.{u,v} $F)) (L R : List (Lit F)) :=
  Q(TwoSided.Derivation $(Denotation.toExprₗ (denotation F ls) L) $(Denotation.toExprₗ (denotation F ls) R))

namespace DerivationQ
open Denotation

variable {F : Q(Type u)} {ls : Q(LogicSymbol $F)} {gz : Q(Gentzen.{u, v} $F)} (L R : List (Lit F))

def DEq {F : Q(Type*)} : Lit F → Lit F → MetaM Bool
  | Litform.atom e,  Litform.atom e'  => Lean.Meta.isDefEq e e'
  | ⊤,               ⊤                => return true
  | ⊥,               ⊥                => return true
  | ~p,              ~p'              => return (← DEq p p')
  | p ⋏ q,           p' ⋏ q'          => return (← DEq p p') && (← DEq q q')
  | p ⋎ q,           p' ⋎ q'          => return (← DEq p p') && (← DEq q q')
  | p ⟶ q,          p' ⟶ q'         => return (← DEq p p') && (← DEq q q')
  | _,               _                => return false

def DMem {F : Q(Type*)} (p : Lit F) (Δ : List (Lit F)) : MetaM Bool :=
  Δ.foldrM (fun q ih => return (←DEq p q) || ih) false

def rotateLeft {p : Lit F} (d : DerivationQ ls gz (L ++ [p]) R) : DerivationQ ls gz (p :: L) R :=
  letI := denotation F ls
  let x : Q(TwoSided.Derivation
    ($(Denotation.toExprₗ (denotation F ls) L) ++ [$(toExpr F p)])
    $(Denotation.toExprₗ (denotation F ls) R)) := d
  q(Gentzen.rotateLeft $x)

def rotateRight {p : Lit F} (d : DerivationQ ls gz L (R ++ [p])) : DerivationQ ls gz L (p :: R) :=
  letI := denotation F ls
  let x : Q(TwoSided.Derivation
    $(Denotation.toExprₗ (denotation F ls) L)
    ($(Denotation.toExprₗ (denotation F ls) R) ++ [$(toExpr F p)])) := d
  q(Gentzen.rotateRight $x)

def verum : DerivationQ ls gz L (⊤ :: R) := q(Gentzen.verum _ _)

def falsum : DerivationQ ls gz (⊥ :: L) R := q(Gentzen.falsum _ _)

def rEmLeftOfEq {p : Lit F} : MetaM (DerivationQ ls gz (p :: L) R) :=
  letI := denotation F ls
  do let some h ← Denotation.memList? (denotation F ls) p R | throwError m! "failed to derive {p} ∈ {R}"
     return q(Gentzen.rEmLeft $h)

def rEmRightOfEq {p : Lit F} : MetaM (DerivationQ ls gz L (p :: R)) :=
  letI := denotation F ls
  do let some h ← Denotation.memList? (denotation F ls) p L | throwError m! "failed to derive {p} ∈ {R}"
     return q(Gentzen.rEmRight $h)

def rNegLeft {p : Lit F} (d : DerivationQ ls gz L (R ++ [p])) : DerivationQ ls gz (~p :: L) R :=
  letI := denotation F ls
  let d : Q(TwoSided.Derivation
    $(Denotation.toExprₗ (denotation F ls) L)
    ($(Denotation.toExprₗ (denotation F ls) R) ++ [$(toExpr F p)])) := d
  q(Gentzen.rNegLeft $d)

def rNegRight {p : Lit F} (d : DerivationQ ls gz (L ++ [p]) R) : DerivationQ ls gz L (~p :: R) :=
  letI := denotation F ls
  let d : Q(TwoSided.Derivation
    ($(Denotation.toExprₗ (denotation F ls) L) ++ [$(toExpr F p)])
    $(Denotation.toExprₗ (denotation F ls) R)) := d
  q(Gentzen.rNegRight $d)

def rAndLeft {p q : Lit F} (d : DerivationQ ls gz (L ++ [p, q]) R) : DerivationQ ls gz (p ⋏ q :: L) R :=
  letI := denotation F ls
  let d : Q(TwoSided.Derivation
    ($(Denotation.toExprₗ (denotation F ls) L) ++ [$(toExpr F p), $(toExpr F q)])
    $(Denotation.toExprₗ (denotation F ls) R)) := d
  q(Gentzen.rAndLeft $d)

def rAndRight {p q : Lit F} (dp : DerivationQ ls gz L (R ++ [p])) (dq : DerivationQ ls gz L (R ++ [q])) :
    DerivationQ ls gz L (p ⋏ q :: R) :=
  letI := denotation F ls
  let dp : Q(TwoSided.Derivation
    $(Denotation.toExprₗ (denotation F ls) L)
    ($(Denotation.toExprₗ (denotation F ls) R) ++ [$(toExpr F p)])) := dp
  let dq : Q(TwoSided.Derivation
    $(Denotation.toExprₗ (denotation F ls) L)
    ($(Denotation.toExprₗ (denotation F ls) R) ++ [$(toExpr F q)])) := dq
  q(Gentzen.rAndRight $dp $dq)

def rOrLeft {p q : Lit F} (dp : DerivationQ ls gz (L ++ [p]) R) (dq : DerivationQ ls gz (L ++ [q]) R) :
    DerivationQ ls gz (p ⋎ q :: L) R :=
  letI := denotation F ls
  let dp : Q(TwoSided.Derivation
    ($(Denotation.toExprₗ (denotation F ls) L) ++ [$(toExpr F p)])
    $(Denotation.toExprₗ (denotation F ls) R)) := dp
  let dq : Q(TwoSided.Derivation
    ($(Denotation.toExprₗ (denotation F ls) L) ++ [$(toExpr F q)])
    $(Denotation.toExprₗ (denotation F ls) R)) := dq
  q(Gentzen.rOrLeft $dp $dq)

def rOrRight {p q : Lit F} (d : DerivationQ ls gz L (R ++ [p, q])) : DerivationQ ls gz L (p ⋎ q :: R) :=
  letI := denotation F ls
  let d : Q(TwoSided.Derivation
    $(Denotation.toExprₗ (denotation F ls) L)
    ($(Denotation.toExprₗ (denotation F ls) R) ++ [$(toExpr F p), $(toExpr F q)])) := d
  q(Gentzen.rOrRight $d)

def rImplyLeft {p q : Lit F} (dp : DerivationQ ls gz L (R ++ [p])) (dq : DerivationQ ls gz (L ++ [q]) R) :
    DerivationQ ls gz ((p ⟶ q) :: L) R :=
  letI := denotation F ls
  let dp : Q(TwoSided.Derivation
    $(Denotation.toExprₗ (denotation F ls) L)
    ($(Denotation.toExprₗ (denotation F ls) R) ++ [$(toExpr F p)])) := dp
  let dq : Q(TwoSided.Derivation
    ($(Denotation.toExprₗ (denotation F ls) L) ++ [$(toExpr F q)])
    $(Denotation.toExprₗ (denotation F ls) R)) := dq
  q(Gentzen.rImplyLeft $dp $dq)

def rImplyRight {p q : Lit F} (d : DerivationQ ls gz (L ++ [p]) (R ++ [q])) : DerivationQ ls gz L ((p ⟶ q) :: R) :=
  letI := denotation F ls
  let d : Q(TwoSided.Derivation
    ($(Denotation.toExprₗ (denotation F ls) L) ++ [$(toExpr F p)])
    ($(Denotation.toExprₗ (denotation F ls) R) ++ [$(toExpr F q)])) := d
  q(Gentzen.rImplyRight $d)

def deriveAux {F : Q(Type u)} (ls : Q(LogicSymbol $F)) (gz : Q(Gentzen.{u, v} $F)) :
    ℕ → Bool → (L R : List (Lit F)) → MetaM (DerivationQ ls gz L R)
  | 0,        _,     L,      R       => throwError m!"failed to prove {L} ⊢ {R}"
  | s + 1,    true,  [],     R       => deriveAux ls gz s false [] R
  | s + 1,    true,  p :: L, R       => do
    --logInfo m!"true: {s}"
    --logInfo (toString (p :: L) ++ " ⊢ " ++ toString R)
    if (←DMem p R) then
      rEmLeftOfEq L R
    else
    match p with
    | ⊤ => return rotateLeft L R (← deriveAux ls gz s false (L ++ [⊤]) R)
    | ⊥ => return falsum L R
    | Litform.atom a => return rotateLeft L R (← deriveAux ls gz s false (L ++ [Litform.atom a]) R)
    | ~p    => do
      let d ← deriveAux ls gz s false L (R ++ [p])
      return rNegLeft L R d
    | p ⋏ q => do
      let d ← deriveAux ls gz s false (L ++ [p, q]) R
      return rAndLeft L R d
    | p ⋎ q => do
      let dp ← deriveAux ls gz s false (L ++ [p]) R
      let dq ← deriveAux ls gz s false (L ++ [q]) R
      return rOrLeft L R dp dq
    | p ⟶ q => do
      let dp ← deriveAux ls gz s false L (R ++ [p])
      let dq ← deriveAux ls gz s false (L ++ [q]) R
      return rImplyLeft L R dp dq
  | s + 1,    false, L,      []      => deriveAux ls gz s true L []
  | s + 1,    false, L,      p :: R  => do
    --logInfo m!"false: {s}"
    --logInfo (toString L ++ " ⊢ " ++ toString [p :: R])
    if (←DMem p L) then
      rEmRightOfEq L R
    else
    match p with
    | ⊤ => return verum L R
    | ⊥ => return rotateRight L R (← deriveAux ls gz s true L (R ++ [⊥]))
    | Litform.atom a => return rotateRight L R (← deriveAux ls gz s true L (R ++ [Litform.atom a]))
    | ~p    => do
      let d ← deriveAux ls gz s true (L ++ [p]) R
      return rNegRight L R d
    | p ⋏ q => do
      let dp ← deriveAux ls gz s true L (R ++ [p])
      let dq ← deriveAux ls gz s true L (R ++ [q])
      return rAndRight L R dp dq
    | p ⋎ q => do
      let d ← deriveAux ls gz s true L (R ++ [p, q])
      return rOrRight L R d
    | p ⟶ q => do
      let d ← deriveAux ls gz s true (L ++ [p]) (R ++ [q])
      return rImplyRight L R d

def derive {F : Q(Type u)} (ls : Q(LogicSymbol $F)) (gz : Q(Gentzen.{u, v} $F)) (s : ℕ) (L R : List (Lit F)) :
    MetaM (DerivationQ ls gz L R) := deriveAux ls gz s true L R

end DerivationQ

def prove {F : Q(Type u)}
    (ls : Q(LogicSymbol $F))
    (sys : Q(System $F)) (_ : Q(LawfulGentzen.{u, v} $F))
    (s : ℕ) (T : Q(Set $F)) (p : Q($F)) : MetaM Q($T ⊢ $p) :=
  letI := Litform.Meta.denotation F ls; do
  let lp : Litform.Meta.Lit F ← Denotation.denote F p
  let d' : Q([] ⊢ᴳ [$p]) ← DerivationQ.derive ls q(LawfulGentzen.toGentzen) s [] [lp]
  let b : Q($T ⊢ $p) := q(LawfulGentzen.toProof $d' $T)
  return b

def prove! {F : Q(Type u)}
    (ls : Q(LogicSymbol $F))
    (sys : Q(System $F)) (_ : Q(LawfulGentzen.{u, v} $F))
    (s : ℕ) (T : Q(Set $F)) (p : Q($F)) : MetaM Q($T ⊢! $p) :=
  letI := Litform.Meta.denotation F ls; do
  let lp : Litform.Meta.Lit F ← Denotation.denote F p
  let d' : Q([] ⊢ᴳ [$p]) ← DerivationQ.derive ls q(LawfulGentzen.toGentzen) s [] [lp]
  let b : Q($T ⊢! $p) := q(⟨LawfulGentzen.toProof $d' $T⟩)
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
  let .some instSys ← trySynthInstanceQ q(System $F)
    | throwError m! "error: failed to find instance System {F}"
  let .some instLGZ ← trySynthInstanceQ q(LawfulGentzen.{u, u} $F)
    | throwError m! "error: failed to find instance LawfulGentzen {F}"
  --logInfo m! "start"
  let b ← prove instLS instSys instLGZ s T p
  Lean.Elab.Tactic.closeMainGoal b

elab "try_prove" n:(num)? : tactic => do
  let s : ℕ :=
    match n with
    | some n => n.getNat
    | none   => 64
  let goalType ← Elab.Tactic.getMainTarget
  let ty ← inferPropQ goalType
  let ~q(@System.Provable $F $j $jj $T $p) := ty | throwError "error: not a type 2"
  let .some instLS ← trySynthInstanceQ (q(LogicSymbol.{u_1} $F) : Q(Type u_1))
    | throwError m! "error: failed to find instance LogicSymbol {F}"
  let .some instSys ← trySynthInstanceQ q(System $F)
    | throwError m! "error: failed to find instance System {F}"
  let .some instLGZ ← trySynthInstanceQ q(LawfulGentzen.{u_1, u_1} $F)
    | throwError m! "error: failed to find instance LawfulGentzen {F}"
  --logInfo m! "start"
  let b ← prove! instLS instSys instLGZ s T p
  Lean.Elab.Tactic.closeMainGoal b

section test
open Propositional Formula
variable (T : Theory ℕ)

example : T ⊢! p ⋎ q ⋎ r ⋎ s ⟷ r ⋎ p ⋎ s ⋎ q ⋎ p := by try_prove

example : T ⊢! p ⟷ p ⋎ p ⋎ p ⋎ p ⋎ p ⋎ p ⋎ p := by try_prove

example : T ⊢! ((p ⟶ q) ⟶ p) ⟶ p := by try_prove

example : T ⊢! (r ⟶ p) ⟶ ((p ⟶ q) ⟶ r) ⟶ p := by try_prove

example : T ⊢! (p ⟶ q) ⋎ (q ⟶ p) := by try_prove

/-
example : T ⊢ p ⟶ p := by tryProve

example : T ⊢ p ⟶ p ⋎ q := by tryProve

example : T ⊢ q ⋎ p ⟷ p ⋎ q := by tryProve

example : T ⊢ ((q ⟶ p) ⟶ q) ⟶ q := by tryProve
-/

end test

end AutoProver

end LO

import Logic.AutoProver.Litform
import Logic.Vorspiel.Meta
import Logic.Propositional.Classical.Basic.Calculus

namespace LO

namespace Gentzen

variable {F : Type*} [LogicalConnective F] [Gentzen F]

variable {Γ Δ : List F} {p q r : F}

def rotateLeft (d : Γ ++ [p] ⊢² Δ) : p :: Γ ⊢² Δ := wk d (by simp) (by simp)

def rotateRight (d : Γ ⊢² Δ ++ [p]) : Γ ⊢² p :: Δ := wk d (by simp) (by simp)

def rEmLeft (h : p ∈ Δ) : p :: Γ ⊢² Δ := closed _ (by simp) h

def rEmRight (h : p ∈ Γ) : Γ ⊢² p :: Δ := closed _ h (by simp)

def rNegLeft (dp : Γ ⊢² Δ ++ [p]) : ~p :: Γ ⊢² Δ :=
  negLeft (wk dp (by simp) (by simp))

def rNegRight (dp : Γ ++ [p] ⊢² Δ) : Γ ⊢² ~p :: Δ :=
  negRight (wk dp (by simp) (by simp))

def rOrLeft (dp : Γ ++ [p] ⊢² Δ) (dq : Γ ++ [q] ⊢² Δ) : p ⋎ q :: Γ ⊢² Δ :=
  orLeft (wk dp (by simp) (by simp)) (wk dq (by simp) (by simp))

def rOrRight (d : Γ ⊢² Δ ++ [p, q]) : Γ ⊢² p ⋎ q :: Δ :=
  orRight (wk d (by simp) $ by simpa using List.subset_cons_of_subset p (List.subset_cons q Δ))

def rAndLeft (d : Γ ++ [p, q] ⊢² Δ) : p ⋏ q :: Γ ⊢² Δ :=
  andLeft (wk d (by simpa using List.subset_cons_of_subset p (List.subset_cons q Γ)) (by simp))

def rAndRight (dp : Γ ⊢² Δ ++ [p]) (dq : Γ ⊢² Δ ++ [q]) : Γ ⊢² p ⋏ q :: Δ :=
  andRight (wk dp (by simp) (by simp)) (wk dq (by simp) (by simp))

def rImplyLeft (dp : Γ ⊢² Δ ++ [p]) (dq : Γ ++ [q] ⊢² Δ) : (p ⟶ q) :: Γ ⊢² Δ :=
  implyLeft (wk dp (by simp) (by simp)) (wk dq (by simp) (by simp))

def rImplyRight (d : Γ ++ [p] ⊢² Δ ++ [q]) : Γ ⊢² (p ⟶ q) :: Δ :=
  implyRight (wk d (by simp) (by simp))

end Gentzen

namespace AutoProver
open Qq Lean Elab Meta Tactic Litform Litform.Meta

#check TwoSided.Derivation

set_option linter.unusedVariables false in
abbrev DerivationQ {F : Q(Type u)} (instLS : Q(LogicalConnective $F)) (instGz : Q(Gentzen $F)) (L R : List (Lit F)) :=
  Q(TwoSided.Derivation $(Denotation.toExprₗ (denotation F instLS) L) $(Denotation.toExprₗ (denotation F instLS) R))

namespace DerivationQ
open Denotation

variable {F : Q(Type u)} {instLS : Q(LogicalConnective $F)} {instGz : Q(Gentzen $F)} (L R : List (Lit F))

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

def rotateLeft {p : Lit F} (d : DerivationQ instLS instGz (L ++ [p]) R) : DerivationQ instLS instGz (p :: L) R :=
  letI := denotation F instLS
  let x : Q(TwoSided.Derivation
    ($(Denotation.toExprₗ (denotation F instLS) L) ++ [$(toExpr F p)])
    $(Denotation.toExprₗ (denotation F instLS) R)) := d
  q(Gentzen.rotateLeft $x)

def rotateRight {p : Lit F} (d : DerivationQ instLS instGz L (R ++ [p])) : DerivationQ instLS instGz L (p :: R) :=
  letI := denotation F instLS
  let x : Q(TwoSided.Derivation
    $(Denotation.toExprₗ (denotation F instLS) L)
    ($(Denotation.toExprₗ (denotation F instLS) R) ++ [$(toExpr F p)])) := d
  q(Gentzen.rotateRight $x)

def verum : DerivationQ instLS instGz L (⊤ :: R) := q(Gentzen.verum _ _)

def falsum : DerivationQ instLS instGz (⊥ :: L) R := q(Gentzen.falsum _ _)

def rEmLeftOfEq {p : Lit F} : MetaM (DerivationQ instLS instGz (p :: L) R) :=
  letI := denotation F instLS
  do let some h ← Denotation.memList? (denotation F instLS) p R | throwError m! "failed to derive {p} ∈ {R}"
     return q(Gentzen.rEmLeft $h)

def rEmRightOfEq {p : Lit F} : MetaM (DerivationQ instLS instGz L (p :: R)) :=
  letI := denotation F instLS
  do let some h ← Denotation.memList? (denotation F instLS) p L | throwError m! "failed to derive {p} ∈ {R}"
     return q(Gentzen.rEmRight $h)

def rNegLeft {p : Lit F} (d : DerivationQ instLS instGz L (R ++ [p])) : DerivationQ instLS instGz (~p :: L) R :=
  letI := denotation F instLS
  let d : Q(TwoSided.Derivation
    $(Denotation.toExprₗ (denotation F instLS) L)
    ($(Denotation.toExprₗ (denotation F instLS) R) ++ [$(toExpr F p)])) := d
  q(Gentzen.rNegLeft $d)

def rNegRight {p : Lit F} (d : DerivationQ instLS instGz (L ++ [p]) R) : DerivationQ instLS instGz L (~p :: R) :=
  letI := denotation F instLS
  let d : Q(TwoSided.Derivation
    ($(Denotation.toExprₗ (denotation F instLS) L) ++ [$(toExpr F p)])
    $(Denotation.toExprₗ (denotation F instLS) R)) := d
  q(Gentzen.rNegRight $d)

def rAndLeft {p q : Lit F} (d : DerivationQ instLS instGz (L ++ [p, q]) R) : DerivationQ instLS instGz (p ⋏ q :: L) R :=
  letI := denotation F instLS
  let d : Q(TwoSided.Derivation
    ($(Denotation.toExprₗ (denotation F instLS) L) ++ [$(toExpr F p), $(toExpr F q)])
    $(Denotation.toExprₗ (denotation F instLS) R)) := d
  q(Gentzen.rAndLeft $d)

def rAndRight {p q : Lit F} (dp : DerivationQ instLS instGz L (R ++ [p])) (dq : DerivationQ instLS instGz L (R ++ [q])) :
    DerivationQ instLS instGz L (p ⋏ q :: R) :=
  letI := denotation F instLS
  let dp : Q(TwoSided.Derivation
    $(Denotation.toExprₗ (denotation F instLS) L)
    ($(Denotation.toExprₗ (denotation F instLS) R) ++ [$(toExpr F p)])) := dp
  let dq : Q(TwoSided.Derivation
    $(Denotation.toExprₗ (denotation F instLS) L)
    ($(Denotation.toExprₗ (denotation F instLS) R) ++ [$(toExpr F q)])) := dq
  q(Gentzen.rAndRight $dp $dq)

def rOrLeft {p q : Lit F} (dp : DerivationQ instLS instGz (L ++ [p]) R) (dq : DerivationQ instLS instGz (L ++ [q]) R) :
    DerivationQ instLS instGz (p ⋎ q :: L) R :=
  letI := denotation F instLS
  let dp : Q(TwoSided.Derivation
    ($(Denotation.toExprₗ (denotation F instLS) L) ++ [$(toExpr F p)])
    $(Denotation.toExprₗ (denotation F instLS) R)) := dp
  let dq : Q(TwoSided.Derivation
    ($(Denotation.toExprₗ (denotation F instLS) L) ++ [$(toExpr F q)])
    $(Denotation.toExprₗ (denotation F instLS) R)) := dq
  q(Gentzen.rOrLeft $dp $dq)

def rOrRight {p q : Lit F} (d : DerivationQ instLS instGz L (R ++ [p, q])) : DerivationQ instLS instGz L (p ⋎ q :: R) :=
  letI := denotation F instLS
  let d : Q(TwoSided.Derivation
    $(Denotation.toExprₗ (denotation F instLS) L)
    ($(Denotation.toExprₗ (denotation F instLS) R) ++ [$(toExpr F p), $(toExpr F q)])) := d
  q(Gentzen.rOrRight $d)

def rImplyLeft {p q : Lit F} (dp : DerivationQ instLS instGz L (R ++ [p])) (dq : DerivationQ instLS instGz (L ++ [q]) R) :
    DerivationQ instLS instGz ((p ⟶ q) :: L) R :=
  letI := denotation F instLS
  let dp : Q(TwoSided.Derivation
    $(Denotation.toExprₗ (denotation F instLS) L)
    ($(Denotation.toExprₗ (denotation F instLS) R) ++ [$(toExpr F p)])) := dp
  let dq : Q(TwoSided.Derivation
    ($(Denotation.toExprₗ (denotation F instLS) L) ++ [$(toExpr F q)])
    $(Denotation.toExprₗ (denotation F instLS) R)) := dq
  q(Gentzen.rImplyLeft $dp $dq)

def rImplyRight {p q : Lit F} (d : DerivationQ instLS instGz (L ++ [p]) (R ++ [q])) : DerivationQ instLS instGz L ((p ⟶ q) :: R) :=
  letI := denotation F instLS
  let d : Q(TwoSided.Derivation
    ($(Denotation.toExprₗ (denotation F instLS) L) ++ [$(toExpr F p)])
    ($(Denotation.toExprₗ (denotation F instLS) R) ++ [$(toExpr F q)])) := d
  q(Gentzen.rImplyRight $d)

def deriveAux {F : Q(Type u)} (instLS : Q(LogicalConnective $F)) (instGz : Q(Gentzen $F)) :
    ℕ → Bool → (L R : List (Lit F)) → MetaM (DerivationQ instLS instGz L R)
  | 0,        _,     L,      R       => throwError m!"failed to prove {L} ⊢ {R}"
  | s + 1,    true,  [],     R       => deriveAux instLS instGz s false [] R
  | s + 1,    true,  p :: L, R       => do
    --logInfo m!"true: {s}"
    --logInfo (toString (p :: L) ++ " ⊢ " ++ toString R)
    if (←DMem p R) then
      rEmLeftOfEq L R
    else
    match p with
    | ⊤ => return rotateLeft L R (← deriveAux instLS instGz s false (L ++ [⊤]) R)
    | ⊥ => return falsum L R
    | Litform.atom a => return rotateLeft L R (← deriveAux instLS instGz s false (L ++ [Litform.atom a]) R)
    | ~p    => do
      let d ← deriveAux instLS instGz s false L (R ++ [p])
      return rNegLeft L R d
    | p ⋏ q => do
      let d ← deriveAux instLS instGz s false (L ++ [p, q]) R
      return rAndLeft L R d
    | p ⋎ q => do
      let dp ← deriveAux instLS instGz s false (L ++ [p]) R
      let dq ← deriveAux instLS instGz s false (L ++ [q]) R
      return rOrLeft L R dp dq
    | p ⟶ q => do
      let dp ← deriveAux instLS instGz s false L (R ++ [p])
      let dq ← deriveAux instLS instGz s false (L ++ [q]) R
      return rImplyLeft L R dp dq
  | s + 1,    false, L,      []      => deriveAux instLS instGz s true L []
  | s + 1,    false, L,      p :: R  => do
    --logInfo m!"false: {s}"
    --logInfo (toString L ++ " ⊢ " ++ toString [p :: R])
    if (←DMem p L) then
      rEmRightOfEq L R
    else
    match p with
    | ⊤ => return verum L R
    | ⊥ => return rotateRight L R (← deriveAux instLS instGz s true L (R ++ [⊥]))
    | Litform.atom a => return rotateRight L R (← deriveAux instLS instGz s true L (R ++ [Litform.atom a]))
    | ~p    => do
      let d ← deriveAux instLS instGz s true (L ++ [p]) R
      return rNegRight L R d
    | p ⋏ q => do
      let dp ← deriveAux instLS instGz s true L (R ++ [p])
      let dq ← deriveAux instLS instGz s true L (R ++ [q])
      return rAndRight L R dp dq
    | p ⋎ q => do
      let d ← deriveAux instLS instGz s true L (R ++ [p, q])
      return rOrRight L R d
    | p ⟶ q => do
      let d ← deriveAux instLS instGz s true (L ++ [p]) (R ++ [q])
      return rImplyRight L R d

def derive {F : Q(Type u)} (instLS : Q(LogicalConnective $F)) (instGz : Q(Gentzen $F)) (s : ℕ) (L R : List (Lit F)) :
    MetaM (DerivationQ instLS instGz L R) := deriveAux instLS instGz s true L R

end DerivationQ

#check @System.Provable

def isExprProvable? (ty : Q(Prop)) : MetaM ((u : Level) × (v : Level) × (_ : Level) × (S : Q(Type u)) × (F : Q(Type v)) × Q($S) × Q($F)) := do
  let ~q(@System.Provable $S $F $instSys $T $p) := ty | throwError m!"error: {ty} not a prop _ ⊢! _"
  return ⟨_, _, u_3, S, F, T, p⟩

section

open Litform.Meta Denotation

variable {S : Q(Type u)} {F : Q(Type v)} (instLS : Q(LogicalConnective $F)) (instSys : Q(System.{v, u, w} $S $F))
  (instGz : Q(Gentzen $F)) (instLTS : Q(LawfulTwoSided $S))


def prove! (s : ℕ) (𝓢 : Q($S)) (p : Q($F)) : MetaM Q($𝓢 ⊢! $p) :=
  letI := Litform.Meta.denotation F instLS; do
  let lp : Litform.Meta.Lit F ← Denotation.denote F p
  let d' : Q([] ⊢² [$p]) ← DerivationQ.derive instLS instGz s [] [lp]
  let b : Q($𝓢 ⊢! $p) := q(⟨LawfulTwoSided.toProofOfNil $d' $𝓢⟩)
  return b

syntax termSeq := "[" (term,*) "]"

def proofOfProvable? (T : Q($S)) (e : Expr) : MetaM ((p : Q($F)) × Q($T ⊢! $p)) := do
  let ⟨ty, h⟩ ← inferPropQ' e
  let ⟨_, _, _, _, _, T', p⟩ ← isExprProvable? ty
  if ← isDefEq T T' then return ⟨p, h⟩
  else throwError m! "failed to find q such that {ty} == {T} ⊢! q"

def proverL₀ (T : Q($S)) (seq : Option (TSyntax `LO.AutoProver.termSeq)) :
    letI := denotation F instLS
    TermElabM ((L₀ : List (Lit F)) × Q(∀ q ∈ $(toExprₗ (denotation F instLS) L₀), $T ⊢! q)) :=
  letI := denotation F instLS; do
  let E ← (match seq with
            | some seq =>
              match seq with
              | `(termSeq| [ $ss,* ] ) => do
                ss.getElems.mapM (fun s => do
                  proofOfProvable? instSys T (← Term.elabTerm s none))
              | _                      => return #[]
            | _        => return #[])
  let E : List ((p : Lit F) × Q($T ⊢! $(toExpr F p))) := Array.toList <| ← E.mapM fun e => do
    let p : Lit F ← denote F e.1
    return ⟨p, e.2⟩
  let L₀ := E.map Sigma.fst
  let H : Q(∀ q ∈ $(toExprₗ (denotation F instLS) L₀), $T ⊢! q)
    ← listSigmaImpliment (denotation F instLS) (p := q(($T ⊢! ·))) E
  return ⟨L₀, H⟩

def proveL₀! (s : ℕ) (T : Q($S)) (p : Q($F))
    (L₀ : List (Lit F)) (H₀ : Q(∀ q ∈ $(toExprₗ (denotation F instLS) L₀), $T ⊢! q)) : MetaM Q($T ⊢! $p) :=
  letI := denotation F instLS; do
  let lp : Lit F ← Denotation.denote F p
  let d' : Q($(toExprₗ (denotation F instLS) L₀) ⊢² [$p])
    ← DerivationQ.derive instLS instGz s L₀ [lp]
  let b : Q($T ⊢! $p) := q(LawfulTwoSided.toProof₁! $d' $H₀)
  return b

end

elab "tautology" n:(num)? : tactic => do
  let s : ℕ :=
    match n with
    | some n => n.getNat
    | none   => 32
  let goalType ← Elab.Tactic.getMainTarget
  let ty ← inferPropQ goalType
  let ⟨u, v, w, S, F, T, p⟩ ← isExprProvable? ty
  let .some instLS ← trySynthInstanceQ q(LogicalConnective $F)
    | throwError m! "error: failed to find instance LogicalConnective {F}"
  let .some instSys ← trySynthInstanceQ q(System.{v,u,w} $S $F)
    | throwError m! "error: failed to find instance System {F}"
  let .some instGz ← trySynthInstanceQ q(Gentzen $F)
    | throwError m! "error: failed to find instance Gentzen {F}"
  let .some instLTS ← trySynthInstanceQ q(LawfulTwoSided $S)
    | throwError m! "error: failed to find instance LawfulTwoSided {F}"
  --logInfo m! "start"
  let b ← prove! instLS instSys instGz instLTS s T p
  Lean.Elab.Tactic.closeMainGoal b

elab "prover" n:(num)? seq:(termSeq)? : tactic => do
  let s : ℕ :=
    match n with
    | some n => n.getNat
    | none   => 32
  let goalType ← Elab.Tactic.getMainTarget
  let ty ← inferPropQ goalType
  let ⟨u, v, w, S, F, T, p⟩ ← isExprProvable? ty
  let .some instLS ← trySynthInstanceQ q(LogicalConnective $F)
    | throwError m! "error: failed to find instance LogicalConnective {F}"
  let .some instSys ← trySynthInstanceQ q(System.{v,u,w} $S $F)
    | throwError m! "error: failed to find instance System {F}"
  let .some instGz ← trySynthInstanceQ q(Gentzen $F)
    | throwError m! "error: failed to find instance Gentzen {F}"
  let .some instLTS ← trySynthInstanceQ q(LawfulTwoSided $S)
    | throwError m! "error: failed to find instance LawfulTwoSided {F}"
  let ⟨L₀, H₀⟩ ← proverL₀ instLS instSys T seq
  let b ← proveL₀! instLS instSys instGz instLTS s T p L₀ H₀
  Lean.Elab.Tactic.closeMainGoal b

end AutoProver

end LO

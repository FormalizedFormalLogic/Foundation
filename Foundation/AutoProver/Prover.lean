import Foundation.AutoProver.Litform
import Foundation.Vorspiel.Meta
import Foundation.Propositional.Classical.Basic.Calculus

-- TODO: fix

namespace LO

namespace Gentzen

variable {F : Type*} [LogicalConnective F] [Gentzen F]

variable {Γ Δ : List F} {φ ψ r : F}

def rEmLeft (h : φ ∈ Δ) : φ :: Γ ⊢² Δ := closed _ (by simp) h

def rEmRight (h : φ ∈ Γ) : Γ ⊢² φ :: Δ := closed _ h (by simp)

def rNegLeft (dp : Γ ⊢² Δ ++ [φ]) : ∼φ :: Γ ⊢² Δ :=
  negLeft (wk dp (by simp) (by simp))

def rNegRight (dp : Γ ++ [φ] ⊢² Δ) : Γ ⊢² ∼φ :: Δ :=
  negRight (wk dp (by simp) (by simp))

def rOrLeft (dp : Γ ++ [φ] ⊢² Δ) (dq : Γ ++ [ψ] ⊢² Δ) : φ ⋎ ψ :: Γ ⊢² Δ :=
  orLeft (wk dp (by simp) (by simp)) (wk dq (by simp) (by simp))

def rOrRight (d : Γ ⊢² Δ ++ [φ, ψ]) : Γ ⊢² φ ⋎ ψ :: Δ :=
  orRight (wk d (by simp) $ by simpa using List.subset_cons_of_subset φ (List.subset_cons ψ Δ))

def rAndLeft (d : Γ ++ [φ, ψ] ⊢² Δ) : φ ⋏ ψ :: Γ ⊢² Δ :=
  andLeft (wk d (by simpa using List.subset_cons_of_subset φ (List.subset_cons ψ Γ)) (by simp))

def rAndRight (dp : Γ ⊢² Δ ++ [φ]) (dq : Γ ⊢² Δ ++ [ψ]) : Γ ⊢² φ ⋏ ψ :: Δ :=
  andRight (wk dp (by simp) (by simp)) (wk dq (by simp) (by simp))

def rImplyLeft (dp : Γ ⊢² Δ ++ [φ]) (dq : Γ ++ [ψ] ⊢² Δ) : (φ ➝ ψ) :: Γ ⊢² Δ :=
  implyLeft (wk dp (by simp) (by simp)) (wk dq (by simp) (by simp))

def rImplyRight (d : Γ ++ [φ] ⊢² Δ ++ [ψ]) : Γ ⊢² (φ ➝ ψ) :: Δ :=
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
  | ∼φ,              ∼φ'              => return (← DEq φ φ')
  | φ ⋏ ψ,           φ' ⋏ ψ'          => return (← DEq φ φ') && (← DEq ψ ψ')
  | φ ⋎ ψ,           φ' ⋎ ψ'          => return (← DEq φ φ') && (← DEq ψ ψ')
  | φ ➝ ψ,          φ' ➝ ψ'         => return (← DEq φ φ') && (← DEq ψ ψ')
  | _,               _                => return false

def DMem {F : Q(Type*)} (φ : Lit F) (Δ : List (Lit F)) : MetaM Bool :=
  Δ.foldrM (fun ψ ih => return (←DEq φ ψ) || ih) false

def rotateLeft {φ : Lit F} (d : DerivationQ instLS instGz (L ++ [φ]) R) : DerivationQ instLS instGz (φ :: L) R :=
  letI := denotation F instLS
  let x : Q(TwoSided.Derivation
    ($(Denotation.toExprₗ (denotation F instLS) L) ++ [$(toExpr F φ)])
    $(Denotation.toExprₗ (denotation F instLS) R)) := d
  ψ(Gentzen.rotateLeft $x)

def rotateRight {φ : Lit F} (d : DerivationQ instLS instGz L (R ++ [φ])) : DerivationQ instLS instGz L (φ :: R) :=
  letI := denotation F instLS
  let x : Q(TwoSided.Derivation
    $(Denotation.toExprₗ (denotation F instLS) L)
    ($(Denotation.toExprₗ (denotation F instLS) R) ++ [$(toExpr F φ)])) := d
  ψ(Gentzen.rotateRight $x)

def verum : DerivationQ instLS instGz L (⊤ :: R) := ψ(Gentzen.verum _ _)

def falsum : DerivationQ instLS instGz (⊥ :: L) R := ψ(Gentzen.falsum _ _)

def rEmLeftOfEq {φ : Lit F} : MetaM (DerivationQ instLS instGz (φ :: L) R) :=
  letI := denotation F instLS
  do let some h ← Denotation.memList? (denotation F instLS) φ R | throwError m! "failed to derive {φ} ∈ {R}"
     return ψ(Gentzen.rEmLeft $h)

def rEmRightOfEq {φ : Lit F} : MetaM (DerivationQ instLS instGz L (φ :: R)) :=
  letI := denotation F instLS
  do let some h ← Denotation.memList? (denotation F instLS) φ L | throwError m! "failed to derive {φ} ∈ {R}"
     return ψ(Gentzen.rEmRight $h)

def rNegLeft {φ : Lit F} (d : DerivationQ instLS instGz L (R ++ [φ])) : DerivationQ instLS instGz (∼φ :: L) R :=
  letI := denotation F instLS
  let d : Q(TwoSided.Derivation
    $(Denotation.toExprₗ (denotation F instLS) L)
    ($(Denotation.toExprₗ (denotation F instLS) R) ++ [$(toExpr F φ)])) := d
  ψ(Gentzen.rNegLeft $d)

def rNegRight {φ : Lit F} (d : DerivationQ instLS instGz (L ++ [φ]) R) : DerivationQ instLS instGz L (∼φ :: R) :=
  letI := denotation F instLS
  let d : Q(TwoSided.Derivation
    ($(Denotation.toExprₗ (denotation F instLS) L) ++ [$(toExpr F φ)])
    $(Denotation.toExprₗ (denotation F instLS) R)) := d
  ψ(Gentzen.rNegRight $d)

def rAndLeft {φ ψ : Lit F} (d : DerivationQ instLS instGz (L ++ [φ, ψ]) R) : DerivationQ instLS instGz (φ ⋏ ψ :: L) R :=
  letI := denotation F instLS
  let d : Q(TwoSided.Derivation
    ($(Denotation.toExprₗ (denotation F instLS) L) ++ [$(toExpr F φ), $(toExpr F ψ)])
    $(Denotation.toExprₗ (denotation F instLS) R)) := d
  ψ(Gentzen.rAndLeft $d)

def rAndRight {φ ψ : Lit F} (dp : DerivationQ instLS instGz L (R ++ [φ])) (dq : DerivationQ instLS instGz L (R ++ [ψ])) :
    DerivationQ instLS instGz L (φ ⋏ ψ :: R) :=
  letI := denotation F instLS
  let dp : Q(TwoSided.Derivation
    $(Denotation.toExprₗ (denotation F instLS) L)
    ($(Denotation.toExprₗ (denotation F instLS) R) ++ [$(toExpr F φ)])) := dp
  let dq : Q(TwoSided.Derivation
    $(Denotation.toExprₗ (denotation F instLS) L)
    ($(Denotation.toExprₗ (denotation F instLS) R) ++ [$(toExpr F ψ)])) := dq
  ψ(Gentzen.rAndRight $dp $dq)

def rOrLeft {φ ψ : Lit F} (dp : DerivationQ instLS instGz (L ++ [φ]) R) (dq : DerivationQ instLS instGz (L ++ [ψ]) R) :
    DerivationQ instLS instGz (φ ⋎ ψ :: L) R :=
  letI := denotation F instLS
  let dp : Q(TwoSided.Derivation
    ($(Denotation.toExprₗ (denotation F instLS) L) ++ [$(toExpr F φ)])
    $(Denotation.toExprₗ (denotation F instLS) R)) := dp
  let dq : Q(TwoSided.Derivation
    ($(Denotation.toExprₗ (denotation F instLS) L) ++ [$(toExpr F ψ)])
    $(Denotation.toExprₗ (denotation F instLS) R)) := dq
  ψ(Gentzen.rOrLeft $dp $dq)

def rOrRight {φ ψ : Lit F} (d : DerivationQ instLS instGz L (R ++ [φ, ψ])) : DerivationQ instLS instGz L (φ ⋎ ψ :: R) :=
  letI := denotation F instLS
  let d : Q(TwoSided.Derivation
    $(Denotation.toExprₗ (denotation F instLS) L)
    ($(Denotation.toExprₗ (denotation F instLS) R) ++ [$(toExpr F φ), $(toExpr F ψ)])) := d
  ψ(Gentzen.rOrRight $d)

def rImplyLeft {φ ψ : Lit F} (dp : DerivationQ instLS instGz L (R ++ [φ])) (dq : DerivationQ instLS instGz (L ++ [ψ]) R) :
    DerivationQ instLS instGz ((φ ➝ ψ) :: L) R :=
  letI := denotation F instLS
  let dp : Q(TwoSided.Derivation
    $(Denotation.toExprₗ (denotation F instLS) L)
    ($(Denotation.toExprₗ (denotation F instLS) R) ++ [$(toExpr F φ)])) := dp
  let dq : Q(TwoSided.Derivation
    ($(Denotation.toExprₗ (denotation F instLS) L) ++ [$(toExpr F ψ)])
    $(Denotation.toExprₗ (denotation F instLS) R)) := dq
  ψ(Gentzen.rImplyLeft $dp $dq)

def rImplyRight {φ ψ : Lit F} (d : DerivationQ instLS instGz (L ++ [φ]) (R ++ [ψ])) : DerivationQ instLS instGz L ((φ ➝ ψ) :: R) :=
  letI := denotation F instLS
  let d : Q(TwoSided.Derivation
    ($(Denotation.toExprₗ (denotation F instLS) L) ++ [$(toExpr F φ)])
    ($(Denotation.toExprₗ (denotation F instLS) R) ++ [$(toExpr F ψ)])) := d
  ψ(Gentzen.rImplyRight $d)

def deriveAux {F : Q(Type u)} (instLS : Q(LogicalConnective $F)) (instGz : Q(Gentzen $F)) :
    ℕ → Bool → (L R : List (Lit F)) → MetaM (DerivationQ instLS instGz L R)
  | 0,        _,     L,      R       => throwError m!"failed to prove {L} ⊢ {R}"
  | s + 1,    true,  [],     R       => deriveAux instLS instGz s false [] R
  | s + 1,    true,  φ :: L, R       => do
    --logInfo m!"true: {s}"
    --logInfo (toString (φ :: L) ++ " ⊢ " ++ toString R)
    if (←DMem φ R) then
      rEmLeftOfEq L R
    else
    match φ with
    | ⊤ => return rotateLeft L R (← deriveAux instLS instGz s false (L ++ [⊤]) R)
    | ⊥ => return falsum L R
    | Litform.atom a => return rotateLeft L R (← deriveAux instLS instGz s false (L ++ [Litform.atom a]) R)
    | ∼φ    => do
      let d ← deriveAux instLS instGz s false L (R ++ [φ])
      return rNegLeft L R d
    | φ ⋏ ψ => do
      let d ← deriveAux instLS instGz s false (L ++ [φ, ψ]) R
      return rAndLeft L R d
    | φ ⋎ ψ => do
      let dp ← deriveAux instLS instGz s false (L ++ [φ]) R
      let dq ← deriveAux instLS instGz s false (L ++ [ψ]) R
      return rOrLeft L R dp dq
    | φ ➝ ψ => do
      let dp ← deriveAux instLS instGz s false L (R ++ [φ])
      let dq ← deriveAux instLS instGz s false (L ++ [ψ]) R
      return rImplyLeft L R dp dq
  | s + 1,    false, L,      []      => deriveAux instLS instGz s true L []
  | s + 1,    false, L,      φ :: R  => do
    --logInfo m!"false: {s}"
    --logInfo (toString L ++ " ⊢ " ++ toString [φ :: R])
    if (←DMem φ L) then
      rEmRightOfEq L R
    else
    match φ with
    | ⊤ => return verum L R
    | ⊥ => return rotateRight L R (← deriveAux instLS instGz s true L (R ++ [⊥]))
    | Litform.atom a => return rotateRight L R (← deriveAux instLS instGz s true L (R ++ [Litform.atom a]))
    | ∼φ    => do
      let d ← deriveAux instLS instGz s true (L ++ [φ]) R
      return rNegRight L R d
    | φ ⋏ ψ => do
      let dp ← deriveAux instLS instGz s true L (R ++ [φ])
      let dq ← deriveAux instLS instGz s true L (R ++ [ψ])
      return rAndRight L R dp dq
    | φ ⋎ ψ => do
      let d ← deriveAux instLS instGz s true L (R ++ [φ, ψ])
      return rOrRight L R d
    | φ ➝ ψ => do
      let d ← deriveAux instLS instGz s true (L ++ [φ]) (R ++ [ψ])
      return rImplyRight L R d

def derive {F : Q(Type u)} (instLS : Q(LogicalConnective $F)) (instGz : Q(Gentzen $F)) (s : ℕ) (L R : List (Lit F)) :
    MetaM (DerivationQ instLS instGz L R) := deriveAux instLS instGz s true L R

end DerivationQ

def isExprProvable? (ty : Q(Prop)) : MetaM ((u : Level) × (v : Level) × (_ : Level) × (F : Q(Type u)) × (S : Q(Type v)) × Q($S) × Q($F)) := do
  let ∼ψ(@System.Provable $F $S $instSys $T $φ) := ty | throwError m!"(isExprProvable?) error: {ty} not a prop _ ⊢! _"
  return ⟨_, _, u_3, F, S, T, φ⟩

section

open Litform.Meta Denotation

variable {F : Q(Type u)} {S : Q(Type v)} (instLS : Q(LogicalConnective $F)) (instSys : Q(System.{u, v, w} $F $S))
  (instGz : Q(Gentzen $F)) (instLTS : Q(LawfulTwoSided $S))

def prove! (s : ℕ) (𝓢 : Q($S)) (φ : Q($F)) : MetaM Q($𝓢 ⊢! $φ) :=
  letI := Litform.Meta.denotation F instLS; do
  let lp : Litform.Meta.Lit F ← Denotation.denote F φ
  let d' : Q([] ⊢² [$φ]) ← DerivationQ.derive instLS instGz s [] [lp]
  let b : Q($𝓢 ⊢! $φ) := ψ(⟨LawfulTwoSided.toProofOfNil $d' $𝓢⟩)
  return b

syntax termSeq := "[" (term,*) "]"

def proofOfProvable? (T : Q($S)) (e : Expr) : MetaM ((φ : Q($F)) × Q($T ⊢! $φ)) := do
  let ⟨ty, h⟩ ← inferPropQ' e
  let ⟨_, _, _, _, _, T', φ⟩ ← isExprProvable? ty
  if ← isDefEq T T' then return ⟨φ, h⟩
  else throwError m! "failed to find ψ such that {ty} == {T} ⊢! ψ"

def proverL₀ (T : Q($S)) (seq : Option (TSyntax `LO.AutoProver.termSeq)) :
    letI := denotation F instLS
    TermElabM ((L₀ : List (Lit F)) × Q(∀ ψ ∈ $(toExprₗ (denotation F instLS) L₀), $T ⊢! ψ)) :=
  letI := denotation F instLS; do
  let E ← (match seq with
            | some seq =>
              match seq with
              | `(termSeq| [ $ss,* ] ) => do
                ss.getElems.mapM (fun s => do
                  --logInfo m! "(proverL₀) s : {s}, elabType: {←Term.elabType s}, elaberm: {← Term.elabTerm s none}"
                  proofOfProvable? instSys T (← Term.elabTerm s none true)) -- TODO: fix
              | _                      => return #[]
            | _        => return #[])
  let E : List ((φ : Lit F) × Q($T ⊢! $(toExpr F φ))) := Array.toList <| ← E.mapM fun e => do
    let φ : Lit F ← denote F e.1
    return ⟨φ, e.2⟩
  let L₀ := E.map Sigma.fst
  let H : Q(∀ ψ ∈ $(toExprₗ (denotation F instLS) L₀), $T ⊢! ψ)
    ← listSigmaImpliment (denotation F instLS) (φ := ψ(($T ⊢! ·))) E
  return ⟨L₀, H⟩

def proveL₀! (s : ℕ) (T : Q($S)) (φ : Q($F))
    (L₀ : List (Lit F)) (H₀ : Q(∀ ψ ∈ $(toExprₗ (denotation F instLS) L₀), $T ⊢! ψ)) : MetaM Q($T ⊢! $φ) :=
  letI := denotation F instLS; do
  let lp : Lit F ← Denotation.denote F φ
  let d' : Q($(toExprₗ (denotation F instLS) L₀) ⊢² [$φ])
    ← DerivationQ.derive instLS instGz s L₀ [lp]
  let b : Q($T ⊢! $φ) := ψ(LawfulTwoSided.toProof₁! $d' $H₀)
  return b

end

elab "tautology" n:(num)? : tactic => do
  let s : ℕ :=
    match n with
    | some n => n.getNat
    | none   => 32
  let goalType ← Elab.Tactic.getMainTarget
  let ty ← inferPropQ goalType
  let ⟨u, v, w, F, S, T, φ⟩ ← isExprProvable? ty
  let .some instLS ← trySynthInstanceQ ψ(LogicalConnective $F)
    | throwError m! "error: failed to find instance LogicalConnective {F}"
  let .some instSys ← trySynthInstanceQ ψ(System.{u,v,w} $F $S)
    | throwError m! "error: failed to find instance System {F}"
  let .some instGz ← trySynthInstanceQ ψ(Gentzen $F)
    | throwError m! "error: failed to find instance Gentzen {F}"
  let .some instLTS ← trySynthInstanceQ ψ(LawfulTwoSided $S)
    | throwError m! "error: failed to find instance LawfulTwoSided {F}"
  --logInfo m! "start"
  let b ← prove! instLS instSys instGz instLTS s T φ
  Lean.Elab.Tactic.closeMainGoal b

elab "prover" n:(num)? seq:(termSeq)? : tactic => do
  let s : ℕ :=
    match n with
    | some n => n.getNat
    | none   => 32
  let goalType ← Elab.Tactic.getMainTarget
  let ty ← inferPropQ goalType
  let ⟨u, v, w, F, S, T, φ⟩ ← isExprProvable? ty
  let .some instLS ← trySynthInstanceQ ψ(LogicalConnective $F)
    | throwError m! "error: failed to find instance LogicalConnective {F}"
  let .some instSys ← trySynthInstanceQ ψ(System.{u,v,w} $F $S)
    | throwError m! "error: failed to find instance System {F}"
  let .some instGz ← trySynthInstanceQ ψ(Gentzen $F)
    | throwError m! "error: failed to find instance Gentzen {F}"
  let .some instLTS ← trySynthInstanceQ ψ(LawfulTwoSided $S)
    | throwError m! "error: failed to find instance LawfulTwoSided {F}"
  let ⟨L₀, H₀⟩ ← proverL₀ instLS instSys T seq
  let b ← proveL₀! instLS instSys instGz instLTS s T φ L₀ H₀
  Lean.Elab.Tactic.closeMainGoal b

end AutoProver

end LO

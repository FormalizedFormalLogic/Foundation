module

public meta import Foundation.Meta.Lit
public meta import Foundation.Meta.TwoSided
public import Foundation.Meta.Lit
public import Foundation.Meta.TwoSided

/-!
# Proof automation based on the proof search on $\mathbf{LK}$
-/

public meta section

namespace LO.Meta

open Mathlib Qq Lean Elab Meta Tactic

namespace ClProver

namespace Theorems

open Entailment TwoSided FiniteContext

variable {F : Type*} [LogicalConnective F] [DecidableEq F] {S : Type*} [Entailment S F] (𝓢 : S) [Entailment.Cl 𝓢]

local notation Γ:45 " ⟹ " Δ:46 => TwoSided 𝓢 Γ Δ

lemma to_provable (φ) (h : [] ⟹ [φ]) : 𝓢 ⊢ φ := TwoSided.to_provable h

lemma rotate_right (Γ Δ φ) (hφ : Γ ⟹ Δ ++ [φ]) : Γ ⟹ φ :: Δ := TwoSided.rotate_right hφ

lemma rotate_left (Γ Δ φ) (hφ : (Γ ++ [φ]) ⟹ Δ) : (φ :: Γ) ⟹ Δ := TwoSided.rotate_left hφ

lemma add_hyp (𝒯 : S) (s : 𝒯 ⪯ 𝓢) (Γ Δ φ) (hφ : 𝒯 ⊢ φ) (h : (φ :: Γ) ⟹ Δ) : Γ ⟹ Δ := TwoSided.add_hyp hφ h

lemma right_closed (Γ Δ φ) (h : φ ∈ Γ) : Γ ⟹ φ :: Δ := TwoSided.right_closed h

lemma left_closed (Γ Δ φ) (h : φ ∈ Δ) : (φ :: Γ) ⟹ Δ := TwoSided.left_closed h

lemma verum_right (Γ Δ) : Γ ⟹ ⊤ :: Δ := TwoSided.verum_right

lemma falsum_left (Γ Δ) : (⊥ :: Γ) ⟹ Δ := TwoSided.falsum_left

lemma falsum_right (Γ Δ) (h : Γ ⟹ Δ) : Γ ⟹ ⊥ :: Δ := TwoSided.falsum_right h

lemma verum_left (Γ Δ) (h : Γ ⟹ Δ) : (⊤ :: Γ) ⟹ Δ := TwoSided.verum_left h

lemma and_right (Γ Δ φ ψ) (hφ : Γ ⟹ Δ ++ [φ]) (hψ : Γ ⟹ Δ ++ [ψ]) : Γ ⟹ φ ⋏ ψ :: Δ :=
  TwoSided.and_right (weakening hφ) (weakening hψ)

lemma or_left (Γ Δ φ ψ) (hφ : (Γ ++ [φ]) ⟹ Δ) (hψ : (Γ ++ [ψ]) ⟹ Δ) : (φ ⋎ ψ :: Γ) ⟹ Δ :=
  TwoSided.or_left (weakening hφ) (weakening hψ)

lemma or_right (Γ Δ φ ψ) (h : Γ ⟹ Δ ++ [φ, ψ]) : Γ ⟹ φ ⋎ ψ :: Δ :=
  TwoSided.or_right (weakening h)

lemma and_left (Γ Δ φ ψ) (h : (Γ ++ [φ, ψ]) ⟹ Δ) : (φ ⋏ ψ :: Γ) ⟹ Δ :=
  TwoSided.and_left (weakening h)

lemma neg_right (Γ Δ φ) (h : (Γ ++ [φ]) ⟹ Δ) : Γ ⟹ ∼φ :: Δ :=
  TwoSided.neg_right_cl (weakening h)

lemma neg_left (Γ Δ φ) (h : Γ ⟹ Δ ++ [φ]) : (∼φ :: Γ) ⟹ Δ :=
  TwoSided.neg_left (weakening h)

lemma imply_right (Γ Δ φ ψ) (h : (Γ ++ [φ]) ⟹ Δ ++ [ψ]) : Γ ⟹ (φ 🡒 ψ) :: Δ :=
  TwoSided.imply_right_cl (weakening h)

lemma imply_left (Γ Δ φ ψ) (hφ : Γ ⟹ Δ ++ [φ]) (hψ : (Γ ++ [ψ]) ⟹ Δ) : ((φ 🡒 ψ) :: Γ) ⟹ Δ :=
  TwoSided.imply_left (weakening hφ) (weakening hψ)

lemma iff_right (Γ Δ φ ψ) (hr : (Γ ++ [φ]) ⟹ Δ ++ [ψ]) (hl : (Γ ++ [ψ]) ⟹ Δ ++ [φ]) : Γ ⟹ (φ 🡘 ψ) :: Δ :=
  TwoSided.iff_right_cl (weakening hr) (weakening hl)

lemma iff_left (Γ Δ φ ψ) (hr : Γ ⟹ Δ ++ [φ, ψ]) (hl : (Γ ++ [φ, ψ]) ⟹ Δ) : ((φ 🡘 ψ) :: Γ) ⟹ Δ :=
  TwoSided.iff_left (weakening hr) (weakening hl)

end Theorems

initialize registerTraceClass `cl_prover

syntax (name := cl_prover) "cl_prover" : tactic

structure Context where
  levelF : Level
  levelS : Level
  levelE : Level
  F : Q(Type levelF)
  LC : Q(LogicalConnective $F)
  DC : Q(DecidableEq $F)
  S : Q(Type levelS)
  E : Q(Entailment.{_, _, levelE} $S $F)
  𝓢 : Q($S)
  CL : Q(Entailment.Cl $𝓢)

/-- The monad for `cl_prover` contains. -/
abbrev M := ReaderT Context AtomM

#check Mathlib.Tactic.AtomM

/-- Apply the function
  `n : ∀ {F} [LogicalConnective F] [DecidableEq F] {S} [Entailment S F] {𝓢} [Entailment.Cl 𝓢], _` to the
implicit parameters in the context, and the given list of arguments. -/
def Context.app (c : Context) (n : Name) : Array Expr → Expr :=
  mkAppN <| @Expr.const n [c.levelF, c.levelS, c.levelE]
    |>.app c.F |>.app c.LC |>.app c.DC |>.app c.S |>.app c.E |>.app c.𝓢 |>.app c.CL

def iapp (n : Name) (xs : Array Expr) : M Expr := do
  let c ← read
  return c.app n xs

def getGoalTwoSided (e : Q(Prop)) : MetaM ((c : Context) × List Q($c.F) × List Q($c.F)) := do
  let ~q(@Entailment.TwoSided $F $LC $S $E $𝓢 $p $q) := e | throwError m!"(getGoal) error: {e} not a form of _ ⊢ _"
  let .some DC ← trySynthInstanceQ q(DecidableEq $F)
    | throwError m! "error: failed to find instance DecidableEq {F}"
  let .some CL ← trySynthInstanceQ q(Entailment.Cl $𝓢)
    | throwError m! "error: failed to find instance Entailment.Cl {𝓢}"
  let Γ ← Qq.ofQList p
  let Δ ← Qq.ofQList q
  return ⟨⟨_, _, _, F, LC, DC, S, E, 𝓢, CL⟩, Γ, Δ⟩

def getGoalProvable (e : Q(Prop)) : MetaM ((c : Context) × Q($c.F)) := do
  let ~q(@Entailment.Provable $F $S $E $𝓢 $p) := e | throwError m!"(getGoal) error: {e} not a form of _ ⊢ _"
  let .some DC ← trySynthInstanceQ q(DecidableEq $F)
    | throwError m! "error: failed to find instance DecidableEq {F}"
  let .some LC ← trySynthInstanceQ q(LogicalConnective $F)
    | throwError m! "error: failed to find instance DecidableEq {F}"
  let .some CL ← trySynthInstanceQ q(Entailment.Cl $𝓢)
    | throwError m! "error: failed to find instance Entailment.Cl {𝓢}"
  return ⟨⟨_, _, _, F, LC, DC, S, E, 𝓢, CL⟩, p⟩

abbrev Sequent := List Lit

def litToExpr (φ : Lit) : M Expr := do
  let c ← read
  return Litform.toExpr c.LC φ

def exprToLit (e : Expr) : M Lit := do
  let c ← read
  Litform.denote c.LC e

def Sequent.toExprList (Γ : Sequent) : M (List Expr) := do
  let c ← read
  return Γ.map (Litform.toExpr c.LC)

def exprListToLitList (l : List Expr) : M (List Lit) := do
  let c ← read
  l.mapM (m := MetaM) (Litform.denote c.LC)

def Sequent.toExpr (Γ : Sequent) : M Expr := do
  let c ← read
  return toQList <| Γ.map (Litform.toExpr c.LC)

def tryRightClose (φ : Lit) (Γ Δ : Sequent) : M (Option Expr) := do
  match ← memQList?' (← litToExpr φ) (← Γ.toExprList) with
  |   .none => return none
  | .some e => do
    let eΓ ← Sequent.toExpr Γ
    let eΔ ← Sequent.toExpr Δ
    let eφ ← litToExpr φ
    return some <| ← iapp ``LO.Meta.ClProver.Theorems.right_closed #[eΓ, eΔ, eφ, e]

def tryLeftClose (φ : Lit) (Γ Δ : Sequent) : M (Option Expr) := do
  match ← memQList?' (← litToExpr φ) (← Δ.toExprList) with
  |   .none => return none
  | .some e => do
    let eΓ ← Sequent.toExpr Γ
    let eΔ ← Sequent.toExpr Δ
    let eφ ← litToExpr φ
    return some <| ← iapp ``LO.Meta.ClProver.Theorems.left_closed #[eΓ, eΔ, eφ, e]

def rotateRight (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  iapp ``LO.Meta.ClProver.Theorems.rotate_right #[eΓ, eΔ, eφ, e]

def rotateLeft (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  iapp ``LO.Meta.ClProver.Theorems.rotate_left #[eΓ, eΔ, eφ, e]

def verumRight (Γ Δ : Sequent) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  iapp ``LO.Meta.ClProver.Theorems.verum_right #[eΓ, eΔ]

def falsumRight (Γ Δ : Sequent) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  iapp ``LO.Meta.ClProver.Theorems.falsum_right #[eΓ, eΔ, e]

def andRight (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  let eψ ← litToExpr ψ
  iapp ``LO.Meta.ClProver.Theorems.and_right #[eΓ, eΔ, eφ, eψ, e₁, e₂]

def orRight (Γ Δ : Sequent) (φ ψ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  let eψ ← litToExpr ψ
  iapp ``LO.Meta.ClProver.Theorems.or_right #[eΓ, eΔ, eφ, eψ, e]

def negRight (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  iapp ``LO.Meta.ClProver.Theorems.neg_right #[eΓ, eΔ, eφ, e]

def implyRight (Γ Δ : Sequent) (φ ψ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  let eψ ← litToExpr ψ
  iapp ``LO.Meta.ClProver.Theorems.imply_right #[eΓ, eΔ, eφ, eψ, e]

def iffRight (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  let eψ ← litToExpr ψ
  iapp ``LO.Meta.ClProver.Theorems.iff_right #[eΓ, eΔ, eφ, eψ, e₁, e₂]


def verumLeft (Γ Δ : Sequent) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  iapp ``LO.Meta.ClProver.Theorems.verum_left #[eΓ, eΔ, e]

def falsumLeft (Γ Δ : Sequent) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  iapp ``LO.Meta.ClProver.Theorems.falsum_left #[eΓ, eΔ]

def andLeft (Γ Δ : Sequent) (φ ψ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  let eψ ← litToExpr ψ
  iapp ``LO.Meta.ClProver.Theorems.and_left #[eΓ, eΔ, eφ, eψ, e]

def orLeft (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  let eψ ← litToExpr ψ
  iapp ``LO.Meta.ClProver.Theorems.or_left #[eΓ, eΔ, eφ, eψ, e₁, e₂]

def negLeft (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  iapp ``LO.Meta.ClProver.Theorems.neg_left #[eΓ, eΔ, eφ, e]

def implyLeft (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  let eψ ← litToExpr ψ
  iapp ``LO.Meta.ClProver.Theorems.imply_left #[eΓ, eΔ, eφ, eψ, e₁, e₂]

def iffLeft (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  let eψ ← litToExpr ψ
  iapp ``LO.Meta.ClProver.Theorems.iff_left #[eΓ, eΔ, eφ, eψ, e₁, e₂]

def toProvable (φ : Expr) (e : Expr) : M Expr := do
  iapp ``LO.Meta.ClProver.Theorems.to_provable #[φ, e]

def prover (k : ℕ) (b : Bool) (Γ Δ : Sequent) : M Expr := do
  --logInfo m!"step: {k}, case: {b}, {← Sequent.toExpr Γ} ⟹ {← Sequent.toExpr Δ}"
  match k, b with
  |     0,      _ => throwError m!"Proof search failed: {← Sequent.toExpr Γ} ⟹ {← Sequent.toExpr Δ}"
  | k + 1,  false =>
    match Δ with
    |     [] => prover k true Γ []
    | φ :: Δ => do
      let e ← tryRightClose φ Γ Δ
      match e with
      | some h => return h
      |   none =>
        match φ with
        | .atom a =>
          let e ← prover k true Γ (Δ ++ [.atom a])
          rotateRight Γ Δ (.atom a) e
        | ⊤ => verumRight Γ Δ
        | ⊥ => do
          let e ← prover k true Γ Δ
          falsumRight Γ Δ e
        | φ ⋏ ψ => do
          let e₁ ← prover k true Γ (Δ ++ [φ])
          let e₂ ← prover k true Γ (Δ ++ [ψ])
          andRight Γ Δ φ ψ e₁ e₂
        | φ ⋎ ψ => do
          let e ← prover k true Γ (Δ ++ [φ, ψ])
          orRight Γ Δ φ ψ e
        | ∼φ => do
          let e ← prover k true (Γ ++ [φ]) Δ
          negRight Γ Δ φ e
        | φ 🡒 ψ => do
          let e ← prover k true (Γ ++ [φ]) (Δ ++ [ψ])
          implyRight Γ Δ φ ψ e
        | .iff φ ψ => do
          let e₁ ← prover k true (Γ ++ [φ]) (Δ ++ [ψ])
          let e₂ ← prover k true (Γ ++ [ψ]) (Δ ++ [φ])
          iffRight Γ Δ φ ψ e₁ e₂
  | k + 1, true =>
    match Γ with
    |     [] => prover k false [] Δ
    | φ :: Γ => do
      let e ← tryLeftClose φ Γ Δ
      match e with
      | some h => return h
      |   none =>
        match φ with
        | .atom a =>
          let e ← prover k false (Γ ++ [.atom a]) Δ
          rotateLeft Γ Δ (.atom a) e
        | ⊤ => do
          let e ← prover k false Γ Δ
          verumLeft Γ Δ e
        | ⊥ => do
          falsumLeft Γ Δ
        | φ ⋏ ψ => do
          let e ← prover k false (Γ ++ [φ, ψ]) Δ
          andLeft Γ Δ φ ψ e
        | φ ⋎ ψ => do
          let e₁ ← prover k false (Γ ++ [φ]) Δ
          let e₂ ← prover k false (Γ ++ [ψ]) Δ
          orLeft Γ Δ φ ψ e₁ e₂
        | ∼φ => do
          let e ← prover k false Γ (Δ ++ [φ])
          negLeft Γ Δ φ e
        | φ 🡒 ψ => do
          let e₁ ← prover k false Γ (Δ ++ [φ])
          let e₂ ← prover k false (Γ ++ [ψ]) Δ
          implyLeft Γ Δ φ ψ e₁ e₂
        | .iff φ ψ => do
          let e₁ ← prover k false Γ (Δ ++ [φ, ψ])
          let e₂ ← prover k false (Γ ++ [φ, ψ]) Δ
          iffLeft Γ Δ φ ψ e₁ e₂

structure HypInfo where
  levelF : Level
  levelS : Level
  levelE : Level
  F : Q(Type levelF)
  S : Q(Type levelS)
  E : Q(Entailment.{_, _, levelE} $S $F)
  𝓢 : Q($S)
  φ : Q($F)
  proof : Q($𝓢 ⊢ $φ)

def synthProvable (e : Expr) : MetaM HypInfo := do
  let (ty : Q(Prop)) ← inferType e
  let ~q(@Entailment.Provable $F $S $E $𝓢 $φ) := ty | throwError m!"(getGoal) error: {e} not a form of _ ⊢ _"
  return ⟨_, _, _, F, S, E, 𝓢, φ, e⟩

structure CompatibleHypInfo where
  𝓢 : Expr
  WT : Expr
  φ : Lit
  proof : Expr

def HypInfo.toCompatible (h : HypInfo) : M CompatibleHypInfo := do
  let c ← read
  if (← isDefEq (← whnf h.F) (← whnf c.F)) && (← isDefEq (← whnf h.S) (← whnf c.S)) && (← isDefEq (← whnf h.E) (← whnf c.E)) then
    let e := @Expr.const ``LO.Entailment.WeakerThan [c.levelF, c.levelS, c.levelS, c.levelE, c.levelE]
      |>.app c.F |>.app c.S |>.app c.S |>.app c.E |>.app c.E |>.app h.𝓢 |>.app c.𝓢
    let .some wt ← trySynthInstance e
      | throwError m! "error: failed to find instance {e}"
    return ⟨h.𝓢, wt, ← exprToLit h.φ, h.proof⟩
  else throwError m! "error: proof not compatible: {h.proof}"

def addHyp (𝓣 wt : Expr) (Γ Δ : Sequent) (φ : Lit) (E e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  iapp ``LO.Meta.ClProver.Theorems.add_hyp #[𝓣, wt, eΓ, eΔ, eφ, E, e]

def addHyps (prover : (Γ Δ : Sequent) → M Expr) (Γ Δ : Sequent) : List HypInfo → M Expr
  |        [] => prover Γ Δ
  | h :: hyps => do
    let H ← h.toCompatible
    addHyp H.𝓢 H.WT Γ Δ H.φ H.proof <| ← addHyps prover (H.φ :: Γ) Δ hyps

def main (n : ℕ) (hyps : Array HypInfo) (L R : List Expr) : M Expr := do
  let Γ ← exprListToLitList L
  let Δ ← exprListToLitList R
  addHyps (prover n false) Γ Δ hyps.toList

syntax termSeq := "[" (term,*) "]"

elab "cl_prover_2s" n:(num)? seq:(termSeq)? : tactic => withMainContext do
  let ⟨c, L, R⟩ ← getGoalTwoSided <| ← whnfR <| ← getMainTarget
  let n : ℕ :=
    match n with
    | some n => n.getNat
    |   none => 32
  let hyps ← (match seq with
    | some seq =>
      match seq with
      | `(termSeq| [ $ss,* ] ) => do
        ss.getElems.mapM fun s ↦ do synthProvable (← Term.elabTerm s none true)
      | _                      =>
        return #[]
    | _        =>
      return #[])
  closeMainGoal `cl_prover <| ← AtomM.run .reducible <| ReaderT.run (main n hyps L R) c

elab "cl_prover" n:(num)? seq:(termSeq)? : tactic => withMainContext do
  let ⟨c, φ⟩ ← getGoalProvable <| ← whnfR <| ← getMainTarget
  let n : ℕ :=
    match n with
    | some n => n.getNat
    |   none => 32
  let hyps ← (match seq with
    | some seq =>
      match seq with
      | `(termSeq| [ $ss,* ] ) => do
        ss.getElems.mapM fun s ↦ do synthProvable (← Term.elabTerm s none true)
      | _                      =>
        return #[]
    | _        =>
      return #[])
  closeMainGoal `cl_prover <| ← AtomM.run .reducible <| ReaderT.run (r := c) do
    let e ← main n hyps [] [φ]
    toProvable φ e

end ClProver

end LO.Meta

end

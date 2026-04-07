module

public meta import Foundation.Meta.Lit
public meta import Foundation.Meta.TwoSided
public import Foundation.Meta.Lit
public import Foundation.Meta.TwoSided

/-!
# Proof automation based on the proof search on (modified) $\mathbf{LJpm}^*$

main reference: Grigori Mints, A Short Introduction to Intuitionistic Logic [Min00]
-/

public meta section

namespace LO.Meta

open Mathlib Qq Lean Elab Meta Tactic

namespace IntProver

namespace Theorems

open Entailment TwoSided Tableaux FiniteContext

variable {F : Type*} [LogicalConnective F] [DecidableEq F] {S : Type*} [Entailment S F] {𝓢 : S} [Entailment.Int 𝓢]

local notation Γ:45 " ⟹ " Δ:46 => TwoSided 𝓢 Γ Δ

scoped notation:0 Γ:45 " ⟶ " Δ:46 => Tableaux.Sequent.mk Γ Δ

set_option linter.unusedSectionVars false in
lemma to_twoSided {Γ Δ} (h : Valid 𝓢 [Γ ⟶ Δ]) : Γ ⟹ Δ := by
  rcases h
  · assumption
  · simp_all

lemma to_provable {φ} (h : Valid 𝓢 [[] ⟶ [φ]]) : 𝓢 ⊢ φ := by
  rcases h
  · exact TwoSided.to_provable <| by assumption
  · simp_all

lemma add_hyp {𝒯 : S} (s : 𝒯 ⪯ 𝓢) {Γ Δ φ} (hφ : 𝒯 ⊢ φ)  : Valid 𝓢 [φ :: Γ ⟶ Δ] → Valid 𝓢 [Γ ⟶ Δ] :=
  Valid.of_single_uppercedent <| TwoSided.add_hyp hφ

lemma right_closed {T Γ Δ φ} (h : φ ∈ Γ) : Valid 𝓢 ((Γ ⟶ φ :: Δ) :: T) := Valid.right_closed h

lemma left_closed {T Γ Δ φ} (h : φ ∈ Δ) : Valid 𝓢 ((φ :: Γ ⟶ Δ) :: T) := Valid.left_closed h

set_option linter.unusedSectionVars false in
lemma remove {T Γ Δ} : Valid 𝓢 T → Valid 𝓢 ((Γ ⟶ Δ) :: T) := Valid.of_subset

set_option linter.unusedSectionVars false in
lemma rotate {T Γ Δ} : Valid 𝓢 (T ++ [Γ ⟶ Δ]) → Valid 𝓢 ((Γ ⟶ Δ) :: T) := Valid.of_subset


lemma remove_right {T Γ Δ φ} : Valid 𝓢 (T ++ [Γ ⟶ Δ]) → Valid 𝓢 ((Γ ⟶ φ :: Δ) :: T) := fun h ↦
  Valid.remove_right (rotate h)

lemma rotate_right {T Γ Δ φ} : Valid 𝓢 (T ++ [Γ ⟶ Δ ++ [φ]]) → Valid 𝓢 ((Γ ⟶ φ :: Δ) :: T) := fun h ↦
  Valid.rotate_right (rotate h)

lemma verum_right {T Γ Δ} : Valid 𝓢 ((Γ ⟶ ⊤ :: Δ) :: T) := Valid.verum_right

lemma falsum_right {T Γ Δ} : Valid 𝓢 (T ++ [Γ ⟶ Δ]) → Valid 𝓢 ((Γ ⟶ ⊥ :: Δ) :: T) := fun h ↦
  Valid.falsum_right (rotate h)

lemma and_right {T Γ Δ φ ψ} :
    Valid 𝓢 (T ++ [Γ ⟶ Δ ++ [φ]]) → Valid 𝓢 (T ++ [Γ ⟶ Δ ++ [ψ]]) → Valid 𝓢 ((Γ ⟶ φ ⋏ ψ :: Δ) :: T) := fun h₁ h₂ ↦
  Valid.and_right (rotate h₁) (rotate h₂)

lemma or_right {T Γ Δ φ ψ} :
    Valid 𝓢 (T ++ [Γ ⟶ Δ ++ [φ, ψ]]) → Valid 𝓢 ((Γ ⟶ φ ⋎ ψ :: Δ) :: T) := fun h ↦
  Valid.or_right (rotate h)

lemma neg_right {T Γ Δ φ} :
    Valid 𝓢 (T ++ [Γ ++ [φ] ⟶ []] ++ [Γ ⟶ Δ]) → Valid 𝓢 ((Γ ⟶ ∼φ :: Δ) :: T) := fun h ↦
  Valid.neg_right' <| rotate <| rotate h

lemma imply_right {T Γ Δ φ ψ} :
    Valid 𝓢 (T ++ [Γ ++ [φ] ⟶ [ψ]] ++ [Γ ⟶ Δ]) → Valid 𝓢 ((Γ ⟶ (φ 🡒 ψ) :: Δ) :: T) := fun h ↦
  Valid.imply_right' <| rotate <| rotate h

lemma iff_right {T Γ Δ φ ψ} :
    Valid 𝓢 (T ++ [Γ ⟶ Δ ++ [φ 🡒 ψ]]) → Valid 𝓢 (T ++ [Γ ⟶ Δ ++ [ψ 🡒 φ]]) → Valid 𝓢 ((Γ ⟶ (φ 🡘 ψ) :: Δ) :: T) := fun h₁ h₂ ↦
  Valid.and_right (rotate h₁) (rotate h₂)


lemma remove_left {T Γ Δ φ} : Valid 𝓢 ((Γ ⟶ Δ) :: T) → Valid 𝓢 ((φ :: Γ ⟶ Δ) :: T) :=
  Valid.remove_left

lemma rotate_left {T Γ Δ φ} : Valid 𝓢 ((Γ ++ [φ] ⟶ Δ) :: T) → Valid 𝓢 ((φ :: Γ ⟶ Δ) :: T) :=
  Valid.rotate_left

lemma verum_left {T Γ Δ} : Valid 𝓢 ((Γ ⟶ Δ) :: T) → Valid 𝓢 ((⊤ :: Γ ⟶ Δ) :: T) := Valid.verum_left

set_option linter.unusedSectionVars false in
lemma falsum_left {T Γ Δ} : Valid 𝓢 ((⊥ :: Γ ⟶ Δ) :: T) := Valid.falsum_left

lemma or_left {T Γ Δ φ ψ} :
    Valid 𝓢 ((Γ ++ [φ] ⟶ Δ) :: T) → Valid 𝓢 ((Γ ++ [ψ] ⟶ Δ) :: T) → Valid 𝓢 ((φ ⋎ ψ :: Γ ⟶ Δ) :: T) :=
  Valid.or_left

lemma and_left {T Γ Δ φ ψ} :
    Valid 𝓢 ((Γ ++ [φ, ψ] ⟶ Δ) :: T) → Valid 𝓢 ((φ ⋏ ψ :: Γ ⟶ Δ) :: T) :=
  Valid.and_left

lemma neg_left {T Γ Δ φ} :
    Valid 𝓢 ((Γ ++ [∼φ] ⟶ Δ ++ [φ]) :: T) → Valid 𝓢 ((∼φ :: Γ ⟶ Δ) :: T) :=
  Valid.neg_left

lemma imply_left {T Γ Δ φ ψ} :
    Valid 𝓢 ((Γ ++ [φ 🡒 ψ] ⟶ Δ ++ [φ]) :: T) → Valid 𝓢 ((Γ ++ [ψ] ⟶ Δ) :: T) → Valid 𝓢 (((φ 🡒 ψ) :: Γ ⟶ Δ) :: T) :=
  Valid.imply_left

lemma iff_left {T Γ Δ φ ψ} :
    Valid 𝓢 ((Γ ++ [φ 🡒 ψ, ψ 🡒 φ] ⟶ Δ) :: T) → Valid 𝓢 (((φ 🡘 ψ) :: Γ ⟶ Δ) :: T) :=
  Valid.and_left

end Theorems

initialize registerTraceClass `int_prover
initialize registerTraceClass `int_prover.detail

structure Context where
  levelF : Level
  levelS : Level
  levelE : Level
  F : Q(Type levelF)
  instLC : Q(LogicalConnective $F)
  instDE : Q(DecidableEq $F)
  S : Q(Type levelS)
  E : Q(Entailment.{_, _, levelE} $S $F)
  𝓢 : Q($S)
  instInt : Q(Entailment.Int $𝓢)

open Mathlib Qq Lean Elab Meta Tactic

/-- The monad for `int_prover` contains. -/
abbrev M := ReaderT Context AtomM

/-- Apply the function
  `n : ∀ {F} [LogicalConnective F] [DecidableEq F] {S} [Entailment S F] {𝓢} [Entailment.Int 𝓢], _` to the
implicit parameters in the context, and the given list of arguments. -/
def Context.app (c : Context) (n : Name) : Array Expr → Expr :=
  mkAppN <| @Expr.const n [c.levelF, c.levelS, c.levelE]
    |>.app c.F |>.app c.instLC |>.app c.instDE |>.app c.S |>.app c.E |>.app c.𝓢 |>.app c.instInt

def iapp (n : Name) (xs : Array Expr) : M Expr := do
  let c ← read
  return c.app n xs

def getGoalTwoSided (e : Q(Prop)) : MetaM ((c : Context) × List Q($c.F) × List Q($c.F)) := do
  let ~q(@Entailment.TwoSided $F $instLC $S $E $𝓢 $p $q) := e | throwError m!"(getGoal) error: {e} not a form of _ ⊢ _"
  let .some instDE ← trySynthInstanceQ q(DecidableEq $F)
    | throwError m! "error: failed to find instance DecidableEq {F}"
  let .some instInt ← trySynthInstanceQ q(Entailment.Int $𝓢)
    | throwError m! "error: failed to find instance Entailment.Cl {𝓢}"
  let Γ ← Qq.ofQList p
  let Δ ← Qq.ofQList q
  return ⟨⟨_, _, _, F, instLC, instDE, S, E, 𝓢, instInt⟩, Γ, Δ⟩

def getGoalProvable (e : Q(Prop)) : MetaM ((c : Context) × Q($c.F)) := do
  let ~q(@Entailment.Provable $F $S $E $𝓢 $p) := e | throwError m!"(getGoal) error: {e} not a form of _ ⊢ _"
  let .some instDE ← trySynthInstanceQ q(DecidableEq $F)
    | throwError m! "error: failed to find instance DecidableEq {F}"
  let .some instLC ← trySynthInstanceQ q(LogicalConnective $F)
    | throwError m! "error: failed to find instance DecidableEq {F}"
  let .some instInt ← trySynthInstanceQ q(Entailment.Int $𝓢)
    | throwError m! "error: failed to find instance Entailment.Cl {𝓢}"
  return ⟨⟨_, _, _, F, instLC, instDE, S, E, 𝓢, instInt⟩, p⟩

abbrev Sequent := List Lit

abbrev Tableaux := Entailment.Tableaux Lit

scoped notation:0 Γ:45 " ⟶ " Δ:46 => Entailment.Tableaux.Sequent.mk Γ Δ

def litToExpr (φ : Lit) : M Expr := do
  let c ← read
  return Litform.toExpr c.instLC φ

def exprToLit (e : Expr) : M Lit := do
  let c ← read
  Litform.denote c.instLC e

def Sequent.toExprList (Γ : Sequent) : M (List Expr) := do
  let c ← read
  return Γ.map (Litform.toExpr c.instLC)

def exprListToLitList (l : List Expr) : M (List Lit) := do
  let c ← read
  l.mapM (m := MetaM) (Litform.denote c.instLC)

def Sequent.toExpr (Γ : Sequent) : M Expr := do
  let c ← read
  return toQList <| Γ.map (Litform.toExpr c.instLC)

def mkTableauSequentQ (F : Q(Type*)) (Γ Δ : Q(List $F)) : Q(Entailment.Tableaux.Sequent $F) :=
  q($Γ ⟶ $Δ)

def Tableaux.toExpr (T : Tableaux) : M Expr := do
  let c ← read
  let m ← T.mapM fun ⟨Γ, Δ⟩ ↦ do
    let Γ ← Sequent.toExpr Γ
    let Δ ← Sequent.toExpr Δ
    let e := mkTableauSequentQ c.F Γ Δ
    return e
  return toQList (u := c.levelF) m

def remove (T : Tableaux) (Γ Δ : Sequent) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  iapp ``LO.Meta.IntProver.Theorems.remove #[T, Γ, Δ, e]

def tryRightClose (T : Tableaux) (Γ Δ : Sequent) (φ : Lit) : M (Option Expr) := do
  match ← memQList?' (← litToExpr φ) (← Γ.toExprList) with
  |   .none => return none
  | .some e => do
    let T ← T.toExpr
    let Γ ← Sequent.toExpr Γ
    let Δ ← Sequent.toExpr Δ
    let φ ← litToExpr φ
    return some <| ← iapp ``LO.Meta.IntProver.Theorems.right_closed #[T, Γ, Δ, φ, e]

def tryLeftClose (T : Tableaux) (Γ Δ : Sequent) (φ : Lit) : M (Option Expr) := do
  match ← memQList?' (← litToExpr φ) (← Δ.toExprList) with
  |   .none => return none
  | .some e => do
    let T ← T.toExpr
    let Γ ← Sequent.toExpr Γ
    let Δ ← Sequent.toExpr Δ
    let φ ← litToExpr φ
    return some <| ← iapp ``LO.Meta.IntProver.Theorems.left_closed #[T, Γ, Δ, φ, e]

def removeRight (T : Tableaux) (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  iapp ``LO.Meta.IntProver.Theorems.remove_right #[T, Γ, Δ, φ, e]

def removeLeft (T : Tableaux) (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  iapp ``LO.Meta.IntProver.Theorems.remove_left #[T, Γ, Δ, φ, e]

def rotateRight (T : Tableaux) (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  iapp ``LO.Meta.IntProver.Theorems.rotate_right #[T, Γ, Δ, φ, e]

def rotateLeft (T : Tableaux) (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  iapp ``LO.Meta.IntProver.Theorems.rotate_left #[T, Γ, Δ, φ, e]

def verumRight (T : Tableaux) (Γ Δ : Sequent) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  iapp ``LO.Meta.IntProver.Theorems.verum_right #[T, Γ, Δ]

def falsumRight (T : Tableaux) (Γ Δ : Sequent) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  iapp ``LO.Meta.IntProver.Theorems.falsum_right #[T, Γ, Δ, e]

def andRight (T : Tableaux) (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  let ψ ← litToExpr ψ
  iapp ``LO.Meta.IntProver.Theorems.and_right #[T, Γ, Δ, φ, ψ, e₁, e₂]

def orRight (T : Tableaux) (Γ Δ : Sequent) (φ ψ : Lit) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  let ψ ← litToExpr ψ
  iapp ``LO.Meta.IntProver.Theorems.or_right #[T, Γ, Δ, φ, ψ, e]

def negRight (T : Tableaux) (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  iapp ``LO.Meta.IntProver.Theorems.neg_right #[T, Γ, Δ, φ, e]

def implyRight (T : Tableaux) (Γ Δ : Sequent) (φ ψ : Lit) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  let ψ ← litToExpr ψ
  iapp ``LO.Meta.IntProver.Theorems.imply_right #[T, Γ, Δ, φ, ψ, e]

def iffRight (T : Tableaux) (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  let ψ ← litToExpr ψ
  iapp ``LO.Meta.IntProver.Theorems.iff_right #[T, Γ, Δ, φ, ψ, e₁, e₂]

def rotate (T : Tableaux) (Γ Δ : Sequent) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  iapp ``LO.Meta.IntProver.Theorems.rotate #[T, Γ, Δ, e]

def verumLeft (T : Tableaux) (Γ Δ : Sequent) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  iapp ``LO.Meta.IntProver.Theorems.verum_left #[T, Γ, Δ, e]

def falsumLeft (T : Tableaux) (Γ Δ : Sequent) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  iapp ``LO.Meta.IntProver.Theorems.falsum_left #[T, Γ, Δ]

def andLeft (T : Tableaux) (Γ Δ : Sequent) (φ ψ : Lit) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  let ψ ← litToExpr ψ
  iapp ``LO.Meta.IntProver.Theorems.and_left #[T, Γ, Δ, φ, ψ, e]

def orLeft (T : Tableaux) (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  let ψ ← litToExpr ψ
  iapp ``LO.Meta.IntProver.Theorems.or_left #[T, Γ, Δ, φ, ψ, e₁, e₂]

def negLeft (T : Tableaux) (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  iapp ``LO.Meta.IntProver.Theorems.neg_left #[T, Γ, Δ, φ, e]

def implyLeft (T : Tableaux) (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  let ψ ← litToExpr ψ
  iapp ``LO.Meta.IntProver.Theorems.imply_left #[T, Γ, Δ, φ, ψ, e₁, e₂]

def iffLeft (T : Tableaux) (Γ Δ : Sequent) (φ ψ : Lit) (e : Expr) : M Expr := do
  let T ← T.toExpr
  let Γ ← Sequent.toExpr Γ
  let Δ ← Sequent.toExpr Δ
  let φ ← litToExpr φ
  let ψ ← litToExpr ψ
  iapp ``LO.Meta.IntProver.Theorems.iff_left #[T, Γ, Δ, φ, ψ, e]

def isWeakerSequent (Γ Δ : Sequent) (T : Tableaux) : M Bool := do
  match T with
  |           [] => return false
  | (Ξ ⟶ Λ) :: T =>
    return ((←Lit.dSubsetList Γ Ξ) && (←Lit.dSubsetList Δ Λ)) || (←isWeakerSequent Γ Δ T)

def prover (k : ℕ) (b : Bool) (T : Tableaux) : M Expr := do
  -- logInfo m!"step: {k}, case: {b}, {← T.toExpr}"
  match k, b with
  |     0,      _ => throwError m!"Proof search failed: {← T.toExpr}"
  | k + 1, false =>
    match T with
    |           [] => throwError m!"Proof search failed: empty tableaux reached."
    | (Γ ⟶ Δ) :: T =>
      if ←isWeakerSequent Γ Δ T then
        let e ← prover k false T
        remove T Γ Δ e
      else
      match Γ with
      |     [] => prover k true (([] ⟶ Δ) :: T)
      | φ :: Γ => do
        match ← tryLeftClose T Γ Δ φ with
        | some h => return h
        |   none => do
          if ← φ.dMem Γ then
            let e ← prover k true ((Γ ⟶ Δ) :: T)
            removeLeft T Γ Δ φ e
          else
          match φ with
          | .atom a => do
            let e ← prover k true ((Γ ++ [.atom a] ⟶ Δ) :: T)
            rotateLeft T Γ Δ (.atom a) e
          | ⊤ => do
            let e ← prover k true ((Γ ⟶ Δ) :: T)
            verumLeft T Γ Δ e
          | ⊥ => do
            falsumLeft T Γ Δ
          | φ ⋏ ψ => do
            let e ← prover k true ((Γ ++ [φ, ψ] ⟶ Δ) :: T)
            andLeft T Γ Δ φ ψ e
          | φ ⋎ ψ => do
            let e₁ ← prover k true ((Γ ++ [φ] ⟶ Δ) :: T)
            let e₂ ← prover k true ((Γ ++ [ψ] ⟶ Δ) :: T)
            orLeft T Γ Δ φ ψ e₁ e₂
          | ∼φ => do
            let e ← prover k true ((Γ ++ [∼φ] ⟶ Δ ++ [φ]) :: T)
            negLeft T Γ Δ φ e
          | φ 🡒 ψ => do
            let e₁ ← prover k true ((Γ ++ [φ 🡒 ψ] ⟶ Δ ++ [φ]) :: T)
            let e₂ ← prover k true ((Γ ++ [ψ] ⟶ Δ) :: T)
            implyLeft T Γ Δ φ ψ e₁ e₂
          | .iff φ ψ => do
            let e ← prover k true ((Γ ++ [φ 🡒 ψ, ψ 🡒 φ] ⟶ Δ) :: T)
            iffLeft T Γ Δ φ ψ e
  | k + 1,  true =>
    match T with
    |                [] => throwError m!"Proof search failed: empty tableaux reached."
    |     (Γ ⟶ Δ) :: T => do
      if ←isWeakerSequent Γ Δ T then
        let e ← prover k false T
        remove T Γ Δ e
      else
      match Δ with
      | [] =>
        let e ← prover k false (T ++ [Γ ⟶ []])
        rotate T Γ [] e
      | φ :: Δ => do
        match ← tryRightClose T Γ Δ φ with
        | some h => return h
        |   none => do
          if ← φ.dMem Δ then
            let e ← prover k false (T ++ [Γ ⟶ Δ])
            removeRight T Γ Δ φ e
          else
          match φ with
          | .atom a => do
            let e ← tryRightClose T Γ Δ (.atom a)
            match e with
            | some h => return h
            |   none => do
              let e ← prover k false (T ++ [Γ ⟶ Δ ++ [.atom a]])
              rotateRight T Γ Δ (.atom a) e
          | ⊤ => verumRight T Γ Δ
          | ⊥ => do
            let e ← prover k false (T ++ [Γ ⟶ Δ])
            falsumRight T Γ Δ e
          | φ ⋏ ψ => do
            let e₁ ← prover k false (T ++ [Γ ⟶ Δ ++ [φ]])
            let e₂ ← prover k false (T ++ [Γ ⟶ Δ ++ [ψ]])
            andRight T Γ Δ φ ψ e₁ e₂
          | φ ⋎ ψ => do
            let e ← prover k false (T ++ [Γ ⟶ Δ ++ [φ, ψ]])
            orRight T Γ Δ φ ψ e
          | ∼φ => do
            let e ← prover k false (T ++ [Γ ++ [φ] ⟶ []] ++ [Γ ⟶ Δ])
            negRight T Γ Δ φ e
          | φ 🡒 ψ => do
            let e ← prover k false (T ++ [Γ ++ [φ] ⟶ [ψ]] ++ [Γ ⟶ Δ])
            implyRight T Γ Δ φ ψ e
          | .iff φ ψ => do
            let e₁ ← prover k false (T ++ [Γ ⟶ Δ ++ [φ 🡒 ψ]])
            let e₂ ← prover k false (T ++ [Γ ⟶ Δ ++ [ψ 🡒 φ]])
            iffRight T Γ Δ φ ψ e₁ e₂

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
  iapp ``LO.Meta.IntProver.Theorems.add_hyp #[𝓣, wt, eΓ, eΔ, eφ, E, e]

def addHyps (prover : (Γ Δ : Sequent) → M Expr) (Γ Δ : Sequent) : List HypInfo → M Expr
  |        [] => prover Γ Δ
  | h :: hyps => do
    let H ← h.toCompatible
    addHyp H.𝓢 H.WT Γ Δ H.φ H.proof <| ← addHyps prover (H.φ :: Γ) Δ hyps

def main (n : ℕ) (hyps : Array HypInfo) (L R : List Expr) : M Expr := do
  let Γ ← exprListToLitList L
  let Δ ← exprListToLitList R
  addHyps (fun Γ Δ ↦ prover n false [Γ ⟶ Δ]) Γ Δ hyps.toList

def toTwoSided (L R : List Expr) (e : Expr) : M Expr := do
  let Γ ← Sequent.toExpr <| ← exprListToLitList L
  let Δ ← Sequent.toExpr <| ← exprListToLitList R
  iapp ``LO.Meta.IntProver.Theorems.to_twoSided #[Γ, Δ, e]

def toProvable (φ : Expr) (e : Expr) : M Expr :=
  iapp ``LO.Meta.IntProver.Theorems.to_provable #[φ, e]

syntax termSeq := "[" (term,*) "]"

elab "int_prover_2s" n:(num)? seq:(termSeq)? : tactic => withMainContext do
  let ⟨c, L, R⟩ ← getGoalTwoSided <| ← whnfR <| ← getMainTarget
  let n : ℕ :=
    match n with
    | some n => n.getNat
    |   none => 64
  let hyps ← (match seq with
    | some seq =>
      match seq with
      | `(termSeq| [ $ss,* ] ) => do
        ss.getElems.mapM fun s ↦ do synthProvable (← Term.elabTerm s none true)
      | _                      =>
        return #[]
    | _        =>
      return #[])
  closeMainGoal `int_prover <| ← AtomM.run .reducible <| ReaderT.run (r := c) do
    let e ← main n hyps L R
    toTwoSided L R e

elab "int_prover" n:(num)? seq:(termSeq)? : tactic => withMainContext do
  let ⟨c, φ⟩ ← getGoalProvable <| ← whnfR <| ← getMainTarget
  let n : ℕ :=
    match n with
    | some n => n.getNat
    |   none => 64
  let hyps ← (match seq with
    | some seq =>
      match seq with
      | `(termSeq| [ $ss,* ] ) => do
        ss.getElems.mapM fun s ↦ do synthProvable (← Term.elabTerm s none true)
      | _                      =>
        return #[]
    | _        =>
      return #[])
  closeMainGoal `int_prover <| ← AtomM.run .reducible <| ReaderT.run (r := c) do
    let e ← main n hyps [] [φ]
    toProvable φ e

end IntProver

end LO.Meta

end

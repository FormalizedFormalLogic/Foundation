import Foundation.Meta.ClProver

/-!
# Proof automation based on the proof search on $\mathbf{LJpm}^*$

main reference: Grigori Mints, A Short Introduction to Intuitionistic Logic
-/

namespace LO.Entailment

variable {F : Type*} [LogicalConnective F] [DecidableEq F] {S : Type*} [Entailment F S]

variable (F)

structure Tabreau.Sequent where
  antecedent : List F
  succedent : List F

abbrev Tabreau := List (Tabreau.Sequent F)

variable {F} (𝓢 : S)

def Tabreau.Valid (τ : Tabreau F) : Prop := ∃ S ∈ τ, TwoSided 𝓢 S.antecedent S.succedent

variable {𝓢}

namespace Tabreau



end Tabreau


/--/
namespace OneSided

set_option linter.unusedSectionVars false

open FiniteContext

variable {𝓢} [Entailment.Int 𝓢]

local notation:40 Γ:47 " ⟹ " φ:46 => Γ ⊢[𝓢]! φ

lemma weakening (h : Γ₁ ⟹ φ) (HΓ : Γ₁ ⊆ Γ₂ := by simp) : Γ₂ ⟹ φ :=
  FiniteContext.weakening! HΓ h

lemma rotate (Γ ξ φ) (hφ : (Γ ++ [φ]) ⟹ ξ) : (φ :: Γ) ⟹ ξ := weakening hφ

lemma rotate_inv (Γ ξ φ) (hφ : (φ :: Γ) ⟹ ξ) : (Γ ++ [φ]) ⟹ ξ := weakening hφ

variable (𝓢)

lemma to_provable (φ) (h : [] ⟹ φ) : 𝓢 ⊢! φ :=
  FiniteContext.provable_iff_provable.mpr h

lemma add_hyp (𝒯 : S) (s : 𝒯 ⪯ 𝓢) (Γ Δ φ) (hφ : 𝒯 ⊢! φ) (h : (φ :: Γ) ⟹ Δ) : Γ ⟹ Δ :=
  deduct! h ⨀! of'! (WeakerThan.pbl hφ)

lemma right_closed (Γ ξ) (h : ξ ∈ Γ) : Γ ⟹ ξ := by_axm! h

lemma verum_right (Γ) : Γ ⟹ ⊤ := by simp

lemma falsum_left (Γ ξ) : (⊥ :: Γ) ⟹ ξ := efq! ⨀! by_axm₀!

lemma verum_left (Γ ξ) (h : Γ ⟹ ξ) : (⊤ :: Γ) ⟹ ξ := weakening h

lemma and_right (Γ φ ψ) (hφ : Γ ⟹ φ) (hψ : Γ ⟹ ψ) : Γ ⟹ φ ⋏ ψ := K!_intro hφ hψ

lemma or_right₁ (Γ φ ψ) (h : Γ ⟹ φ) : Γ ⟹ φ ⋎ ψ := A!_intro_left h

lemma or_right₂ (Γ φ ψ) (h : Γ ⟹ ψ) : Γ ⟹ φ ⋎ ψ := A!_intro_right h

lemma imply_right (Γ φ ψ) (h : Γ ++ [φ] ⟹ ψ) : Γ ⟹ φ ➝ ψ := deduct_iff.mpr <| rotate _ _ _ h

lemma or_left (Γ Δ φ ψ) (hφ : (Γ ++ [φ]) ⟹ Δ) (hψ : (Γ ++ [ψ]) ⟹ Δ) : (φ ⋎ ψ :: Γ) ⟹ Δ := by
  apply deductInv!
  apply left_A!_intro
  · apply deduct! (rotate_left _ _ _ hφ)
  · apply deduct! (rotate_left _ _ _ hψ)

  have : Γ ⊢[𝓢]! (φ :: ψ :: Δ).disj ➝ (φ ⋎ ψ :: Δ).disj := by
    apply left_Disj!_intro
    intro χ hχ
    rcases show χ = φ ∨ χ = ψ ∨ χ ∈ Δ by simpa using hχ with (rfl | rfl | hχ)
    · apply right_Disj!_intro' (χ ⋎ ψ :: Δ) (φ := χ ⋎ ψ) (by simp) or₁!
    · apply right_Disj!_intro' (φ ⋎ χ :: Δ) (φ := φ ⋎ χ) (by simp) or₂!
    · apply right_Disj!_intro _ (by simp [hχ])
  exact this ⨀! (weakening h)

lemma and_left (Γ Δ φ ψ) (h : (Γ ++ [φ, ψ]) ⟹ Δ) : (φ ⋏ ψ :: Γ) ⟹ Δ := by
  have h : (φ :: ψ :: Γ) ⟹ Δ := weakening h
  have : (φ ⋏ ψ :: Γ) ⊢[𝓢]! ψ ➝ φ ➝ Δ.disj := wk! (by simp) (deduct! <| deduct! h)
  exact this ⨀! (deductInv! and₂!) ⨀! (deductInv! and₁!)

lemma neg_right (Γ Δ φ) (h : (Γ ++ [φ]) ⟹ Δ) : Γ ⟹ ∼φ :: Δ := by
  have hφ : Γ ⊢[𝓢]! φ ➝ (∼φ :: Δ).disj := by
    apply deduct!
    suffices (φ :: Γ) ⊢[𝓢]! Δ.disj ➝ (∼φ :: Δ).disj from this ⨀ rotate_left Γ Δ φ h
    apply left_Disj!_intro
    intro ψ hψ
    apply right_Disj!_intro _ (by simp [hψ])
  have hnφ : Γ ⊢[𝓢]! ∼φ ➝ (∼φ :: Δ).disj := right_Disj!_intro _ (by simp)
  exact left_A!_intro hφ hnφ ⨀ lem!

lemma neg_left (Γ Δ φ) (h : Γ ⟹ Δ ++ [φ]) : (∼φ :: Γ) ⟹ Δ := by
  suffices (∼φ :: Γ) ⊢[𝓢]! (φ :: Δ).disj ➝ Δ.disj from this ⨀ (wk! (by simp) (rotate_right _ _ _ h))
  apply left_Disj!_intro
  intro ψ hψ
  rcases show ψ = φ ∨ ψ ∈ Δ by simpa using hψ with (rfl | hψ)
  · apply deductInv!
    exact CNC!
  · apply right_Disj!_intro _ (by simp [hψ])

lemma imply_right (Γ Δ φ ψ) (h : (Γ ++ [φ]) ⟹ Δ ++ [ψ]) : Γ ⟹ (φ ➝ ψ) :: Δ := by
  have h : (φ :: Γ) ⟹ ψ :: Δ := weakening h
  have hnφ : Γ ⊢[𝓢]! ∼φ ➝ ((φ ➝ ψ) :: Δ).disj := by
    apply right_Disj!_intro' ((φ ➝ ψ) :: Δ) (φ := φ ➝ ψ) (by simp)
    exact CNC!
  have hφ : Γ ⊢[𝓢]! φ ➝ ((φ ➝ ψ) :: Δ).disj := by
    apply deduct!
    suffices (φ :: Γ) ⊢[𝓢]! (ψ :: Δ).disj ➝ ((φ ➝ ψ) :: Δ).disj from this ⨀ h
    apply left_Disj!_intro
    intro χ hχ
    rcases show χ = ψ ∨ χ ∈ Δ by simpa using hχ with (rfl | hχ)
    · apply right_Disj!_intro' _ (φ := φ ➝ χ) (by simp)
      exact imply₁!
    · apply right_Disj!_intro
      simp [hχ]
  exact left_A!_intro hφ hnφ ⨀ lem!

lemma imply_left (Γ Δ φ ψ) (hφ : Γ ⟹ Δ ++ [φ]) (hψ : (Γ ++ [ψ]) ⟹ Δ) : ((φ ➝ ψ) :: Γ) ⟹ Δ := by
  --apply deductInv!
  suffices ((φ ➝ ψ) :: Γ) ⊢[𝓢]! (φ :: Δ).disj ➝ Δ.disj from this ⨀! wk! (by simp) (rotate_right Γ Δ φ hφ)
  apply left_Disj!_intro
  intro χ hχ
  rcases show χ = φ ∨ χ ∈ Δ by simpa using hχ with (rfl | hχ)
  · apply deduct!
    have : Γ ⊢[𝓢]! ψ ➝ Δ.disj := deduct! (rotate_left Γ Δ ψ hψ)
    apply (wk! (by simp) this) ⨀! (by_axm₁! ⨀! by_axm₀!)
  · apply right_Disj!_intro _ (by simp [hχ])

lemma iff_right (Γ Δ φ ψ) (hr : (Γ ++ [φ]) ⟹ Δ ++ [ψ]) (hl : (Γ ++ [ψ]) ⟹ Δ ++ [φ]) : Γ ⟹ (φ ⭤ ψ) :: Δ := by
  apply and_right
  · apply rotate_right_inv
    apply imply_right
    assumption
  · apply rotate_right_inv
    apply imply_right
    assumption

lemma iff_left (Γ Δ φ ψ) (hr : Γ ⟹ Δ ++ [φ, ψ]) (hl : (Γ ++ [φ, ψ]) ⟹ Δ) : ((φ ⭤ ψ) :: Γ) ⟹ Δ := by
  apply and_left
  suffices ((φ ➝ ψ) :: (ψ ➝ φ) :: Γ) ⟹ Δ from weakening this
  apply imply_left
  · apply imply_left
    · simpa using hr
    · suffices (φ :: Γ) ⟹ φ :: Δ from weakening this
      apply deductInv!
      apply right_Disj!_intro _ (by simp)
  · apply imply_left
    · suffices (ψ :: Γ) ⟹ ψ :: Δ from weakening this
      apply deductInv!
      apply right_Disj!_intro _ (by simp)
    · exact weakening hl

end TwoSided

end LO.Entailment

namespace LO.Meta

open Mathlib Qq Lean Elab Meta Tactic

namespace ClProver

initialize registerTraceClass `cl_prover
initialize registerTraceClass `cl_prover.detail

syntax (name := cl_prover) "cl_prover" : tactic

structure Context where
  levelF : Level
  levelS : Level
  levelE : Level
  F : Q(Type levelF)
  LC : Q(LogicalConnective $F)
  DC : Q(DecidableEq $F)
  S : Q(Type levelS)
  E : Q(Entailment.{_, _, levelE} $F $S)
  𝓢 : Q($S)
  CL : Q(Entailment.Cl $𝓢)

/-- The monad for `cl_prover` contains. -/
abbrev M := ReaderT Context AtomM

/-- Apply the function
  `n : ∀ {F} [LogicalConnective F] [DecidableEq F] {S} [Entailment F S] {𝓢} [Entailment.Cl 𝓢], _` to the
implicit parameters in the context, and the given list of arguments. -/
def Context.app (c : Context) (n : Name) : Array Expr → Expr :=
  mkAppN <| @Expr.const n [c.levelF, c.levelS, c.levelE]
    |>.app c.F |>.app c.LC |>.app c.DC |>.app c.S |>.app c.E |>.app c.𝓢 |>.app c.CL

def iapp (n : Name) (xs : Array Expr) : M Expr := do
  let c ← read
  return c.app n xs

def getGoalTwoSided (e : Q(Prop)) : MetaM ((c : Context) × List Q($c.F) × List Q($c.F)) := do
  let ~q(@Entailment.TwoSided $F $LC $S $E $𝓢 $p $q) := e | throwError m!"(getGoal) error: {e} not a form of _ ⊢! _"
  let .some DC ← trySynthInstanceQ q(DecidableEq $F)
    | throwError m! "error: failed to find instance DecidableEq {F}"
  let .some CL ← trySynthInstanceQ q(Entailment.Cl $𝓢)
    | throwError m! "error: failed to find instance Entailment.Cl {𝓢}"
  let Γ ← Qq.ofQList p
  let Δ ← Qq.ofQList q
  return ⟨⟨_, _, _, F, LC, DC, S, E, 𝓢, CL⟩, Γ, Δ⟩

def getGoalProvable (e : Q(Prop)) : MetaM ((c : Context) × Q($c.F)) := do
  let ~q(@Entailment.Provable $F $S $E $𝓢 $p) := e | throwError m!"(getGoal) error: {e} not a form of _ ⊢! _"
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
    return some <| ← iapp ``LO.Entailment.TwoSided.right_closed #[eΓ, eΔ, eφ, e]

def tryLeftClose (φ : Lit) (Γ Δ : Sequent) : M (Option Expr) := do
  match ← memQList?' (← litToExpr φ) (← Δ.toExprList) with
  |   .none => return none
  | .some e => do
    let eΓ ← Sequent.toExpr Γ
    let eΔ ← Sequent.toExpr Δ
    let eφ ← litToExpr φ
    return some <| ← iapp ``LO.Entailment.TwoSided.left_closed #[eΓ, eΔ, eφ, e]

def rotateRight (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  iapp ``LO.Entailment.TwoSided.rotate_right #[eΓ, eΔ, eφ, e]

def rotateLeft (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  iapp ``LO.Entailment.TwoSided.rotate_left #[eΓ, eΔ, eφ, e]

def verumRight (Γ Δ : Sequent) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  iapp ``LO.Entailment.TwoSided.verum_right #[eΓ, eΔ]

def falsumRight (Γ Δ : Sequent) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  iapp ``LO.Entailment.TwoSided.falsum_right #[eΓ, eΔ, e]

def andRight (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  let eψ ← litToExpr ψ
  iapp ``LO.Entailment.TwoSided.and_right #[eΓ, eΔ, eφ, eψ, e₁, e₂]

def orRight (Γ Δ : Sequent) (φ ψ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  let eψ ← litToExpr ψ
  iapp ``LO.Entailment.TwoSided.or_right #[eΓ, eΔ, eφ, eψ, e]

def negRight (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  iapp ``LO.Entailment.TwoSided.neg_right #[eΓ, eΔ, eφ, e]

def implyRight (Γ Δ : Sequent) (φ ψ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  let eψ ← litToExpr ψ
  iapp ``LO.Entailment.TwoSided.imply_right #[eΓ, eΔ, eφ, eψ, e]

def iffRight (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  let eψ ← litToExpr ψ
  iapp ``LO.Entailment.TwoSided.iff_right #[eΓ, eΔ, eφ, eψ, e₁, e₂]


def verumLeft (Γ Δ : Sequent) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  iapp ``LO.Entailment.TwoSided.verum_left #[eΓ, eΔ, e]

def falsumLeft (Γ Δ : Sequent) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  iapp ``LO.Entailment.TwoSided.falsum_left #[eΓ, eΔ]

def andLeft (Γ Δ : Sequent) (φ ψ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  let eψ ← litToExpr ψ
  iapp ``LO.Entailment.TwoSided.and_left #[eΓ, eΔ, eφ, eψ, e]

def orLeft (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  let eψ ← litToExpr ψ
  iapp ``LO.Entailment.TwoSided.or_left #[eΓ, eΔ, eφ, eψ, e₁, e₂]

def negLeft (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  iapp ``LO.Entailment.TwoSided.neg_left #[eΓ, eΔ, eφ, e]

def implyLeft (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  let eψ ← litToExpr ψ
  iapp ``LO.Entailment.TwoSided.imply_left #[eΓ, eΔ, eφ, eψ, e₁, e₂]

def iffLeft (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← litToExpr φ
  let eψ ← litToExpr ψ
  iapp ``LO.Entailment.TwoSided.iff_left #[eΓ, eΔ, eφ, eψ, e₁, e₂]

def toProvable (φ : Expr) (e : Expr) : M Expr := do
  iapp ``LO.Entailment.TwoSided.to_provable #[φ, e]

def prover (k : ℕ) (b : Bool) (Γ Δ : Sequent) : M Expr := do
  --logInfo m!"step: {k}, case: {b}, {← Sequent.toExpr Γ} ⟹ {← Sequent.toExpr Δ}"
  match k, b with
  |     0,      _ => throwError m!"Proof search failed: {← Sequent.toExpr Γ} ⟹ {← Sequent.toExpr Δ}"
  | k + 1,  false =>
    match Δ with
    |    .atom a :: Δ => do
      let e ← tryRightClose (.atom a) Γ Δ
      match e with
      | some h =>
        return h
      |   none => do
        let e ← prover k true Γ (Δ ++ [.atom a])
        rotateRight Γ Δ (.atom a) e
    |          ⊤ :: Δ => verumRight Γ Δ
    |          ⊥ :: Δ => do
      let e ← prover k true Γ Δ
      falsumRight Γ Δ e
    |      φ ⋏ ψ :: Δ => do
      let e₁ ← prover k true Γ (Δ ++ [φ])
      let e₂ ← prover k true Γ (Δ ++ [ψ])
      andRight Γ Δ φ ψ e₁ e₂
    |      φ ⋎ ψ :: Δ => do
      let e ← prover k true Γ (Δ ++ [φ, ψ])
      orRight Γ Δ φ ψ e
    |         ∼φ :: Δ => do
      let e ← prover k true (Γ ++ [φ]) Δ
      negRight Γ Δ φ e
    |    (φ ➝ ψ) :: Δ => do
      let e ← prover k true (Γ ++ [φ]) (Δ ++ [ψ])
      implyRight Γ Δ φ ψ e
    | (.iff φ ψ) :: Δ => do
      let e₁ ← prover k true (Γ ++ [φ]) (Δ ++ [ψ])
      let e₂ ← prover k true (Γ ++ [ψ]) (Δ ++ [φ])
      iffRight Γ Δ φ ψ e₁ e₂
    |              [] =>
      prover k true Γ []
  | k + 1, true =>
    match Γ with
    |    .atom a :: Γ => do
      let e ← tryLeftClose (.atom a) Γ Δ
      match e with
      | some h =>
        return h
      |   none => do
        let e ← prover k false (Γ ++ [.atom a]) Δ
        rotateLeft Γ Δ (.atom a) e
    |          ⊤ :: Γ => do
      let e ← prover k false Γ Δ
      verumLeft Γ Δ e
    |          ⊥ :: Γ => do
      falsumLeft Γ Δ
    |      φ ⋏ ψ :: Γ => do
      let e ← prover k false (Γ ++ [φ, ψ]) Δ
      andLeft Γ Δ φ ψ e
    |      φ ⋎ ψ :: Γ => do
      let e₁ ← prover k false (Γ ++ [φ]) Δ
      let e₂ ← prover k false (Γ ++ [ψ]) Δ
      orLeft Γ Δ φ ψ e₁ e₂
    |         ∼φ :: Γ => do
      let e ← prover k false Γ (Δ ++ [φ])
      negLeft Γ Δ φ e
    |    (φ ➝ ψ) :: Γ => do
      let e₁ ← prover k false Γ (Δ ++ [φ])
      let e₂ ← prover k false (Γ ++ [ψ]) Δ
      implyLeft Γ Δ φ ψ e₁ e₂
    | (.iff φ ψ) :: Γ => do
      let e₁ ← prover k false Γ (Δ ++ [φ, ψ])
      let e₂ ← prover k false (Γ ++ [φ, ψ]) Δ
      iffLeft Γ Δ φ ψ e₁ e₂
    |              [] =>
      prover k false [] Δ

structure HypInfo where
  levelF : Level
  levelS : Level
  levelE : Level
  F : Q(Type levelF)
  S : Q(Type levelS)
  E : Q(Entailment.{_, _, levelE} $F $S)
  𝓢 : Q($S)
  φ : Q($F)
  proof : Q($𝓢 ⊢! $φ)

def synthProvable (e : Expr) : MetaM HypInfo := do
  let (ty : Q(Prop)) ← inferType e
  let ~q(@Entailment.Provable $F $S $E $𝓢 $φ) := ty | throwError m!"(getGoal) error: {e} not a form of _ ⊢! _"
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
  iapp ``LO.Entailment.TwoSided.add_hyp #[𝓣, wt, eΓ, eΔ, eφ, E, e]

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

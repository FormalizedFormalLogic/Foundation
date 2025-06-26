import Foundation.Logic.Calculus
import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.Propositional.Hilbert.WellKnown
import Foundation.Meta.Qq
import Foundation.Meta.Lit

namespace LO.Entailment

variable {F : Type*} [LogicalConnective F] [DecidableEq F] {S : Type*} [Entailment F S]

variable (𝓢 : S)

abbrev TwoSided (Γ Δ : List F) : Prop := Γ ⊢[𝓢]! Δ.disj

namespace TwoSided

open FiniteContext

variable {𝓢} [Entailment.Cl 𝓢]

local notation Γ:45 " ⟹ " Δ:46 => TwoSided 𝓢 Γ Δ

lemma provable_of (h : [] ⟹ [φ]) : 𝓢 ⊢! φ :=
  FiniteContext.provable_iff_provable.mpr <| left_Disj!_intro [φ] (by simp) ⨀! h

lemma weakening (h : Γ₁ ⟹ Δ₁) (HΓ : Γ₁ ⊆ Γ₂ := by simp) (HΔ : Δ₁ ⊆ Δ₂ := by simp) : Γ₂ ⟹ Δ₂ :=
  FiniteContext.weakening! HΓ <| left_Disj!_intro Δ₁ (fun _ hψ ↦ right_Disj!_intro _ (HΔ hψ)) ⨀! h

lemma rotate_right (Γ Δ φ) (hφ : Γ ⟹ Δ ++ [φ]) : Γ ⟹ φ :: Δ := weakening hφ

lemma rotate_left (Γ Δ φ) (hφ : (Γ ++ [φ]) ⟹ Δ) : (φ :: Γ) ⟹ Δ := weakening hφ

lemma rotate_right_inv (Γ Δ φ) (hφ : Γ ⟹ φ :: Δ) : Γ ⟹ Δ ++ [φ] := weakening hφ

lemma rotate_left_inv (Γ Δ φ) (hφ : (φ :: Γ) ⟹ Δ) : (Γ ++ [φ]) ⟹ Δ := weakening hφ

variable (𝓢)

lemma right_closed (Γ Δ φ) (h : φ ∈ Γ) : Γ ⟹ φ :: Δ := right_Disj!_intro _ (φ := φ) (by simp) ⨀! (by_axm! h)

lemma left_closed (Γ Δ φ) (h : φ ∈ Δ) : (φ :: Γ) ⟹ Δ := right_Disj!_intro _ (φ := φ) h ⨀! by_axm!

lemma verum_right (Γ Δ) : Γ ⟹ ⊤ :: Δ := right_Disj!_intro _ (φ := ⊤) (by simp) ⨀! (by simp)

lemma falsum_left (Γ Δ) : (⊥ :: Γ) ⟹ Δ := efq! ⨀! by_axm₀!

lemma falsum_right (Γ Δ) (h : Γ ⟹ Δ) : Γ ⟹ ⊥ :: Δ := weakening h

lemma verum_left (Γ Δ) (h : Γ ⟹ Δ) : (⊤ :: Γ) ⟹ Δ := weakening h

lemma and_right (Γ Δ φ ψ) (hφ : Γ ⟹ Δ ++ [φ]) (hψ : Γ ⟹ Δ ++ [ψ]) : Γ ⟹ φ ⋏ ψ :: Δ := by
  have : Γ ⊢[𝓢]! (φ :: Δ).disj ➝ (ψ :: Δ).disj ➝ (φ ⋏ ψ :: Δ).disj := by
    apply left_Disj!_intro
    rintro χ hχ
    rcases show χ = φ ∨ χ ∈ Δ by simpa using hχ with (rfl | hχ)
    · apply deduct!
      apply left_Disj!_intro
      intro ξ hξ
      rcases show ξ = ψ ∨ ξ ∈ Δ by simpa using hξ with (rfl | hξ)
      · apply deduct!
        apply right_Disj!_intro (χ ⋏ ξ :: Δ) (φ := χ ⋏ ξ) List.mem_cons_self ⨀! (K!_intro by_axm₁! by_axm₀!)
      · apply right_Disj!_intro _ (by simp [hξ])
    · apply deduct!
      apply dhyp!
      apply right_Disj!_intro _ (φ := χ) (by simp [hχ]) ⨀! by_axm₀!
  exact this ⨀! rotate_right _ _ _ hφ ⨀! rotate_right _ _ _ hψ

lemma or_left (Γ Δ φ ψ) (hφ : (Γ ++ [φ]) ⟹ Δ) (hψ : (Γ ++ [ψ]) ⟹ Δ) : (φ ⋎ ψ :: Γ) ⟹ Δ := by
  apply deductInv!
  apply left_A!_intro
  · apply deduct! (rotate_left _ _ _ hφ)
  · apply deduct! (rotate_left _ _ _ hψ)

lemma or_right (Γ Δ φ ψ) (h : Γ ⟹ Δ ++ [φ, ψ]) : Γ ⟹ φ ⋎ ψ :: Δ := by
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

abbrev Sequent := List Lit

def Lit.toExpr (φ : Lit) : M Expr := do
  let c ← read
  return Litform.toExpr c.LC φ

def Sequent.toExprList (Γ : Sequent) : M (List Expr) := do
  let c ← read
  return Γ.map (Litform.toExpr c.LC)

def Sequent.toExpr (Γ : Sequent) : M Expr := do
  let c ← read
  return toQList <| Γ.map (Litform.toExpr c.LC)

def tryRightClose (φ : Lit) (Γ Δ : Sequent) : M (Option Expr) := do
  match ← memQList?' (← Lit.toExpr φ) (← Γ.toExprList) with
  |   .none => return none
  | .some e => do
    let eΓ ← Sequent.toExpr Γ
    let eΔ ← Sequent.toExpr Δ
    let eφ ← Lit.toExpr φ
    return some <| ← iapp ``LO.Entailment.TwoSided.right_closed #[eΓ, eΔ, eφ, e]

def tryLeftClose (φ : Lit) (Γ Δ : Sequent) : M (Option Expr) := do
  match ← memQList?' (← Lit.toExpr φ) (← Δ.toExprList) with
  |   .none => return none
  | .some e => do
    let eΓ ← Sequent.toExpr Γ
    let eΔ ← Sequent.toExpr Δ
    let eφ ← Lit.toExpr φ
    return some <| ← iapp ``LO.Entailment.TwoSided.left_closed #[eΓ, eΔ, eφ, e]

def rotateRight (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← Lit.toExpr φ
  iapp ``LO.Entailment.TwoSided.rotate_right #[eΓ, eΔ, eφ, e]

def rotateLeft (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← Lit.toExpr φ
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
  let eφ ← Lit.toExpr φ
  let eψ ← Lit.toExpr ψ
  iapp ``LO.Entailment.TwoSided.and_right #[eΓ, eΔ, eφ, eψ, e₁, e₂]

def orRight (Γ Δ : Sequent) (φ ψ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← Lit.toExpr φ
  let eψ ← Lit.toExpr ψ
  iapp ``LO.Entailment.TwoSided.or_right #[eΓ, eΔ, eφ, eψ, e]

def negRight (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← Lit.toExpr φ
  iapp ``LO.Entailment.TwoSided.neg_right #[eΓ, eΔ, eφ, e]

def implyRight (Γ Δ : Sequent) (φ ψ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← Lit.toExpr φ
  let eψ ← Lit.toExpr ψ
  iapp ``LO.Entailment.TwoSided.imply_right #[eΓ, eΔ, eφ, eψ, e]

def iffRight (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← Lit.toExpr φ
  let eψ ← Lit.toExpr ψ
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
  let eφ ← Lit.toExpr φ
  let eψ ← Lit.toExpr ψ
  iapp ``LO.Entailment.TwoSided.and_left #[eΓ, eΔ, eφ, eψ, e]

def orLeft (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← Lit.toExpr φ
  let eψ ← Lit.toExpr ψ
  iapp ``LO.Entailment.TwoSided.or_left #[eΓ, eΔ, eφ, eψ, e₁, e₂]

def negLeft (Γ Δ : Sequent) (φ : Lit) (e : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← Lit.toExpr φ
  iapp ``LO.Entailment.TwoSided.neg_left #[eΓ, eΔ, eφ, e]

def implyLeft (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← Lit.toExpr φ
  let eψ ← Lit.toExpr ψ
  iapp ``LO.Entailment.TwoSided.imply_left #[eΓ, eΔ, eφ, eψ, e₁, e₂]

def iffLeft (Γ Δ : Sequent) (φ ψ : Lit) (e₁ e₂ : Expr) : M Expr := do
  let eΓ ← Sequent.toExpr Γ
  let eΔ ← Sequent.toExpr Δ
  let eφ ← Lit.toExpr φ
  let eψ ← Lit.toExpr ψ
  iapp ``LO.Entailment.TwoSided.iff_left #[eΓ, eΔ, eφ, eψ, e₁, e₂]

def search (k : ℕ) (b : Bool) (Γ Δ : Sequent) : M Expr := do
  logInfo m!"step: {k}, case: {b}, {Γ} ⟹ {Δ}"
  match k, b with
  |     0,      _ => throwError m!"auto prove failed: {Γ} ⟹ {Δ}"
  | k + 1,  false =>
    match Δ with
    |    .atom a :: Δ => do
      let e ← tryRightClose (.atom a) Γ Δ
      match e with
      | some h =>
        logInfo m!"case: GOAL CLOSED R: {a}"
        return h
      |   none => do
        let e ← search k true Γ (Δ ++ [.atom a])
        rotateRight Γ Δ (.atom a) e
    |          ⊤ :: Δ => verumRight Γ Δ
    |          ⊥ :: Δ => do
      logInfo m!"case: ⊥_R"
      let e ← search k true Γ Δ
      falsumRight Γ Δ e
    |      φ ⋏ ψ :: Δ => do
      let e₁ ← search k true Γ (Δ ++ [φ])
      let e₂ ← search k true Γ (Δ ++ [ψ])
      andRight Γ Δ φ ψ e₁ e₂
    |      φ ⋎ ψ :: Δ => do
      let e ← search k true Γ (Δ ++ [φ, ψ])
      orRight Γ Δ φ ψ e
    |         ∼φ :: Δ => do
      let e ← search k true (Γ ++ [φ]) Δ
      negRight Γ Δ φ e
    |    (φ ➝ ψ) :: Δ => do
      logInfo m!"case: imply_R"
      let e ← search k true (Γ ++ [φ]) (Δ ++ [ψ])
      implyRight Γ Δ φ ψ e
    | (.iff φ ψ) :: Δ => do
      logInfo m!"case: iff_R"
      let e₁ ← search k true (Γ ++ [φ]) (Δ ++ [ψ])
      let e₂ ← search k true (Γ ++ [ψ]) (Δ ++ [φ])
      iffRight Γ Δ φ ψ e₁ e₂
    |              [] =>
      search k true Γ []
  | k + 1, true =>
    match Γ with
    |    .atom a :: Γ => do
      let e ← tryLeftClose (.atom a) Γ Δ
      match e with
      | some h =>
        logInfo m!"case: GOAL CLOSED L: {a}"
        return h
      |   none => do
        let e ← search k false (Γ ++ [.atom a]) Δ
        rotateLeft Γ Δ (.atom a) e
    |          ⊤ :: Γ => do
      let e ← search k false Γ Δ
      verumLeft Γ Δ e
    |          ⊥ :: Γ => do
      falsumLeft Γ Δ
    |      φ ⋏ ψ :: Γ => do
      let e ← search k false (Γ ++ [φ, ψ]) Δ
      andLeft Γ Δ φ ψ e
    |      φ ⋎ ψ :: Γ => do
      let e₁ ← search k false (Γ ++ [φ]) Δ
      let e₂ ← search k false (Γ ++ [ψ]) Δ
      orLeft Γ Δ φ ψ e₁ e₂
    |         ∼φ :: Γ => do
      let e ← search k false Γ (Δ ++ [φ])
      negLeft Γ Δ φ e
    |    (φ ➝ ψ) :: Γ => do
      logInfo m!"case: imply_L"
      let e₁ ← search k false Γ (Δ ++ [φ])
      let e₂ ← search k false (Γ ++ [ψ]) Δ
      implyLeft Γ Δ φ ψ e₁ e₂
    | (.iff φ ψ) :: Γ => do
      logInfo m!"case: iff_L"
      let e₁ ← search k false Γ (Δ ++ [φ, ψ])
      let e₂ ← search k false (Γ ++ [φ, ψ]) Δ
      iffLeft Γ Δ φ ψ e₁ e₂
    |              [] =>
      search k false [] Δ

elab "cl_prover_2s" n:(num)? : tactic => withMainContext do
  let n : ℕ :=
    match n with
    | some n => n.getNat
    | none   => 32
  let ⟨c, L, R⟩ ← getGoalTwoSided <| ← whnfR <| ← getMainTarget
  let Γ ← L.mapM (m := MetaM) (Litform.denote c.LC)
  let Δ ← R.mapM (m := MetaM) (Litform.denote c.LC)
  --logInfo m!"{Γ} ⟹ {Δ}"
  closeMainGoal `cl_prover <| ← AtomM.run .reducible <| ReaderT.run (search n false Γ Δ) c

macro "cl_prover" n:(num)? : tactic => do
  match n with
  | some n => `(tactic| apply LO.Entailment.TwoSided.provable_of <;> cl_prover_2s $n)
  | none   => `(tactic| apply LO.Entailment.TwoSided.provable_of <;> cl_prover_2s)

section

section

variable {F : Type*} [DecidableEq F] {S : Type*} [LogicalConnective F] [Entailment F S]

variable {𝓢 : S} [Entailment.Cl 𝓢] {φ ψ : F}

example : Entailment.TwoSided 𝓢 [φ, ψ] [χ ⋏ ξ, χ, ψ] := by cl_prover_2s

example : Entailment.TwoSided 𝓢 [φ ⭤ ψ] [φ ➝ (χ ⋎ ψ)] := by cl_prover_2s

example : Entailment.TwoSided 𝓢 [⊥] [⊥] := by cl_prover_2s

example : Entailment.TwoSided 𝓢 [φ ⭤ ψ, χ ⭤ ξ] [(ψ ➝ ξ) ⭤ (φ ➝ χ)] := by cl_prover_2s 32

example : 𝓢 ⊢! (φ ⋏ ψ) ➝ ((φ ➝ ψ ➝ ⊥) ➝ ⊥) := by
  cl_prover

example : 𝓢 ⊢! ((φ ⭤ ψ) ⋏ (χ ⭤ ξ)) ➝ ((ψ ➝ ξ) ⭤ (φ ➝ χ)) := by
  cl_prover

end
section

open LO.Propositional

variable {φ ψ χ : Formula ℕ}

example : Entailment.TwoSided Hilbert.Cl [φ ⋏ ⊤, ψ] [ψ, φ, .atom 9] := by { cl_prover_2s }

end

end

end ClProver

end LO.Meta

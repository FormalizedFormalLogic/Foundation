import Foundation.Logic.Calculus
import Foundation.Logic.HilbertStyle.Supplemental
import Foundation.Vorspiel.Meta
import Mathlib.Tactic.TryThis
import Mathlib.Util.AtomM
import Foundation.Propositional.Hilbert.WellKnown

inductive DbgResult (α : Type u) : α → Type u
  | intro : (a b : α) → a = b → DbgResult α a

instance {α} (a : α) : ToString (DbgResult α a) := ⟨fun r =>
  match r with
  | DbgResult.intro _ _ _ => "🎉 Proof Success! 🎉"⟩

namespace Qq

open Mathlib Qq Lean Elab Meta Tactic

def rflQ {α : Q(Sort u)} (a : Q($α)) : Q($a = $a) := q(rfl)

def toQList {α : Q(Type u)} : List Q($α) → Q(List $α)
  |     [] => q([])
  | a :: v => q($a :: $(toQList v))

lemma List.mem_of_eq {a b : α} {l} (h : a = b) : a ∈ b :: l := by simp [h]

lemma List.mem_of_mem {a b : α} {l : List α} (h : a ∈ l) : a ∈ b :: l := by simp [h]

lemma List.mem_singleton_of_eq (a b : α) (h : a = b) : a ∈ [b] := by simp [h]

def memQList? {α : Q(Type u)} (a : Q($α)) : (l : List Q($α)) → MetaM <| Option Q($a ∈ $(toQList l))
  |     [] => return none
  | b :: l => do
      if (← isDefEq (← whnf a) (← whnf b)) then
        let e : Q($a = $b) := rflQ a
        return some q(List.mem_of_eq $e)
      else
        let some h ← memQList? a l | return none
        return some q(List.mem_of_mem $h)

def memQList?' (a : Expr) (l : List Expr) : MetaM (Option Expr) := do
  let ⟨u, _, a⟩ ← inferTypeQ' a
  memQList? (u := u) a l

partial def ofQList {α : Q(Type u)} (l : Q(List $α)) : MetaM <| List Q($α) := do
  match l with
  |       ~q([]) => return []
  | ~q($a :: $l) => return a :: (← ofQList l)

end Qq

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

lemma rotate (hφ : Γ ⟹ Δ ++ [φ]) : Γ ⟹ φ :: Δ := weakening hφ

lemma and_right (Γ Δ φ ψ) (hφ : Γ ⟹ φ :: Δ) (hψ : Γ ⟹ ψ :: Δ) : Γ ⟹ φ ⋏ ψ :: Δ := by
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
  exact this ⨀! hφ ⨀! hψ

variable (𝓢)

lemma right_closed (Γ φ Δ) (h : φ ∈ Γ) : Γ ⟹ φ :: Δ := right_Disj!_intro _ (φ := φ) (by simp) ⨀! (by_axm! h)

lemma left_closed (Γ φ Δ) (h : φ ∈ Δ) : (φ :: Γ) ⟹ Δ := right_Disj!_intro _ (φ := φ) h ⨀! by_axm!

end TwoSided

end LO.Entailment

namespace LO.Meta

open Mathlib Qq Lean Elab Meta Tactic

inductive Litform (α : Type*) : Type _
  | atom (a : α)  : Litform α
  | verum         : Litform α
  | falsum        : Litform α
  | and           : Litform α → Litform α → Litform α
  | or            : Litform α → Litform α → Litform α
  | neg           : Litform α → Litform α
  | imply         : Litform α → Litform α → Litform α
  | iff           : Litform α → Litform α → Litform α

namespace Litform

instance : LogicalConnective (Litform α) where
  top   := Litform.verum
  bot   := Litform.falsum
  wedge := Litform.and
  vee   := Litform.or
  tilde := Litform.neg
  arrow := Litform.imply

section ToString

variable [ToString α]

def toStr : Litform α → String
  |       ⊤ => "⊤"
  |       ⊥ => "⊥"
  |  atom a => s!"atom {toString a}"
  |      ∼φ => "(¬" ++ toStr φ ++ ")"
  |   φ ⋏ ψ => "(" ++ toStr φ ++ " ∧ " ++ toStr ψ ++ ")"
  |   φ ⋎ ψ => "(" ++ toStr φ ++ " ∨ "  ++ toStr ψ ++ ")"
  |   φ ➝ ψ => "(" ++ toStr φ ++ " → "  ++ toStr ψ ++ ")"
  | iff φ ψ => "(" ++ toStr φ ++ " ↔ "  ++ toStr ψ ++ ")"

instance : Repr (Litform α) := ⟨fun t _ => toStr t⟩

instance : ToString (Litform α) := ⟨toStr⟩

end ToString

variable (F : Q(Type*)) (ls : Q(LogicalConnective $F))

abbrev _root_.LO.Meta.Lit := Litform Expr

variable {F}

abbrev toExpr : Lit → Q($F)
  |  atom e => e
  |       ⊤ => q(⊤)
  |       ⊥ => q(⊥)
  |   φ ⋏ ψ => q($(toExpr φ) ⋏ $(toExpr ψ))
  |   φ ⋎ ψ => q($(toExpr φ) ⋎ $(toExpr ψ))
  |      ∼φ => q(∼$(toExpr φ))
  |   φ ➝ ψ => q($(toExpr φ) ➝ $(toExpr ψ))
  | iff φ ψ => q($(toExpr φ) ⭤ $(toExpr ψ))

partial def summands {α : Q(Type $u)} (inst : Q(Add $α)) :
    Q($α) → MetaM (List Q($α))
  | ~q($x + $y) => return (← summands inst x) ++ (← summands inst y)
  | n => return [n]

partial def denote : Q($F) → MetaM Lit
  |       ~q(⊤) => return ⊤
  |       ~q(⊥) => return ⊥
  | ~q($φ ⋏ $ψ) => return (←denote φ) ⋏ (←denote ψ)
  | ~q($φ ⋎ $ψ) => return (←denote φ) ⋎ (←denote ψ)
  | ~q($φ ➝ $ψ) => return (←denote φ) ➝ (←denote ψ)
  | ~q($φ ⭤ $ψ) => return iff (←denote φ) (←denote ψ)
  |     ~q(∼$φ) => return ∼(←denote φ)
  |      ~q($e) => return atom e

variable (F)

end Litform

namespace CLProver

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

#check Entailment.TwoSided.right_closed
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

def code (Γ Δ : Sequent) : M Expr := do
  match Δ with
  |     [] => throwError m!"mssg: {Γ} ⟹ {Δ} found"
  | φ :: Δ =>
    logInfo m!"case: {φ} :: {Δ}"
    match ← memQList?' (← Lit.toExpr φ) (← Γ.toExprList) with
    | .none => throwError m! "FAILED: {φ} ∉ {Γ}"
    | .some e => do
      let eΔ ← Sequent.toExpr Δ
      let eΓ ← Sequent.toExpr Γ
      let eφ ← Lit.toExpr φ
      logInfo m!"e : {e}"
      let k ← iapp ``LO.Entailment.TwoSided.right_closed #[eΓ, eφ, eΔ, e]
      logInfo m!"k : {k}"
      iapp ``LO.Entailment.TwoSided.right_closed #[eΓ, eφ, eΔ, e]


elab "test2s" : tactic => withMainContext do
  let ⟨c, L, R⟩ ← getGoalTwoSided <| ← whnfR <| ← getMainTarget
  let Γ ← L.mapM (m := MetaM) (Litform.denote c.LC)
  let Δ ← R.mapM (m := MetaM) (Litform.denote c.LC)
  logInfo m!"{Γ} ⟹ {Δ}"
  closeMainGoal `cl_prover <| ← AtomM.run .reducible <| ReaderT.run (code Γ Δ) c

section

section

variable {F : Type*} [DecidableEq F] {S : Type*} [LogicalConnective F] [Entailment F S]

variable {𝓢 : S} [Entailment.Cl 𝓢] {φ ψ : F}

example : Entailment.TwoSided 𝓢 [φ ⋏ ⊤, ψ] [ψ, φ] := by { test2s }

end
section

open LO.Propositional

variable {φ ψ χ : Formula ℕ}

example : Entailment.TwoSided Hilbert.Cl [φ ⋏ ⊤, ψ] [ψ, φ, .atom 9] := by { test2s }

end

end

end CLProver

end LO.Meta

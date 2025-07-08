import Foundation.Meta.Qq
import Foundation.Logic.LogicSymbol

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

def toStr [ToString α] : Litform α → String
  |       ⊤ => "⊤"
  |       ⊥ => "⊥"
  |  atom a => s!"atom {toString a}"
  |      ∼φ => "(¬" ++ toStr φ ++ ")"
  |   φ ⋏ ψ => "(" ++ toStr φ ++ " ∧ " ++ toStr ψ ++ ")"
  |   φ ⋎ ψ => "(" ++ toStr φ ++ " ∨ "  ++ toStr ψ ++ ")"
  |   φ ➝ ψ => "(" ++ toStr φ ++ " → "  ++ toStr ψ ++ ")"
  | iff φ ψ => "(" ++ toStr φ ++ " ↔ "  ++ toStr ψ ++ ")"

instance [ToString α] : ToString (Litform α) := ⟨toStr⟩


def format [Repr α] : Litform α → Format
  |       ⊤ => s!"⊤"
  |       ⊥ => s!"⊥"
  |  atom a => repr a
  |      ∼φ => s!"(¬{format φ})"
  |   φ ⋏ ψ => s!"({format φ} ∧ {format ψ})"
  |   φ ⋎ ψ => s!"({format φ} ∨ {format ψ})"
  |   φ ➝ ψ => s!"({format φ} → {format ψ})"
  | iff φ ψ => s!"({format φ} ↔ {format ψ})"

instance [Repr α] : Repr (Litform α) := ⟨fun t _ ↦ format t⟩

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

@[simp] def complexity : Litform α → ℕ
  |  atom _ => 0
  |       ⊤ => 0
  |       ⊥ => 0
  |   φ ⋏ ψ => max φ.complexity ψ.complexity + 1
  |   φ ⋎ ψ => max φ.complexity ψ.complexity + 1
  |      ∼φ => φ.complexity + 1
  |   φ ➝ ψ => max φ.complexity ψ.complexity + 1
  | iff φ ψ => max φ.complexity ψ.complexity + 1

end Litform

namespace Lit

def DEq : Lit → Lit → MetaM Bool
  |    .atom e,   .atom e' => Lean.Meta.isDefEq e e'
  |          ⊤,          ⊤ => return true
  |          ⊥,          ⊥ => return true
  |         ∼φ,         ∼ψ => return (← DEq φ ψ)
  |    φ₁ ⋏ ψ₁,    φ₂ ⋏ ψ₂ => return (← DEq φ₁ φ₂) && (← DEq ψ₁ ψ₂)
  |    φ₁ ⋎ ψ₁,    φ₂ ⋎ ψ₂ => return (← DEq φ₁ φ₂) && (← DEq ψ₁ ψ₂)
  |    φ₁ ➝ ψ₁,    φ₂ ➝ ψ₂ => return (← DEq φ₁ φ₂) && (← DEq ψ₁ ψ₂)
  | .iff φ₁ ψ₁, .iff φ₂ ψ₂ => return (← DEq φ₁ φ₂) && (← DEq ψ₁ ψ₂)
  |          _,          _ => return false

def dMem (φ : Lit) (Δ : List Lit) : MetaM Bool :=
  Δ.foldrM (fun ψ ih ↦ return (←DEq φ ψ) || ih) false

def dSubsetList (Γ Δ : List Lit) : MetaM Bool := do
  match Γ with
  |     [] => return true
  | φ :: Γ => return (←φ.dMem Γ) && (←dSubsetList Γ Δ)

end Lit

end LO.Meta

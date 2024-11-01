import Foundation.Logic.Calculus
import Foundation.Vorspiel.Meta

open Qq Lean Elab Meta Tactic

namespace LO

inductive Litform (α : Type*) : Type _
  | atom (a : α)  : Litform α
  | verum         : Litform α
  | falsum        : Litform α
  | and           : Litform α → Litform α → Litform α
  | or            : Litform α → Litform α → Litform α
  | neg           : Litform α → Litform α
  | imply         : Litform α → Litform α → Litform α

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
  | ⊤      => "⊤"
  | ⊥      => "⊥"
  | atom a => toString a
  | ∼φ     => "(¬" ++ toStr φ ++ ")"
  | φ ⋏ ψ  => "(" ++ toStr φ ++ " ∧ " ++ toStr ψ ++ ")"
  | φ ⋎ ψ  => "(" ++ toStr φ ++ " ∨ "  ++ toStr ψ ++ ")"
  | φ ➝ ψ => "(" ++ toStr φ ++ " ➝ "  ++ toStr ψ ++ ")"

instance : Repr (Litform α) := ⟨fun t _ => toStr t⟩

instance : ToString (Litform α) := ⟨toStr⟩

end ToString

namespace Meta

variable (F : Q(Type*)) (ls : Q(LogicalConnective $F))

abbrev Lit (F : Q(Type*)) := Litform Q($F)

abbrev toExpr : Lit F → Q($F)
  | atom e  => ψ($e)
  | ⊤       => ψ(⊤)
  | ⊥       => ψ(⊥)
  | φ ⋏ ψ   => ψ($(toExpr φ) ⋏ $(toExpr ψ))
  | φ ⋎ ψ   => ψ($(toExpr φ) ⋎ $(toExpr ψ))
  | ∼φ      => ψ(∼$(toExpr φ))
  | φ ➝ ψ  => ψ($(toExpr φ) ➝ $(toExpr ψ))

partial def denote : Q($F) → MetaM (Lit F)
  | ∼ψ(⊤)        => return ⊤
  | ∼ψ(⊥)        => return ⊥
  | ∼ψ($φ ⋏ $ψ)  => return (←denote φ) ⋏ (←denote ψ)
  | ∼ψ($φ ⋎ $ψ)  => return (←denote φ) ⋎ (←denote ψ)
  | ∼ψ($φ ➝ $ψ) => return (←denote φ) ➝ (←denote ψ)
  | ∼ψ($φ ⭤ $ψ)  => return (←denote φ) ⭤ (←denote ψ)
  | ∼ψ(∼$φ)      => return ∼(←denote φ)
  | ∼ψ($e)       => return atom e

instance denotation : Denotation ψ($F) (Lit F) where
  denote' := denote F ls
  toExpr' := toExpr F ls

abbrev DEq (φ ψ : Lit F) :=
  letI := denotation F ls
  Denotation.DEq F φ ψ

end Meta

end Litform

end LO

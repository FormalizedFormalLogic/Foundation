import Logic.Logic.Calculus
import Logic.Vorspiel.Meta

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
  | ~p     => "(¬" ++ toStr p ++ ")"
  | p ⋏ q  => "(" ++ toStr p ++ " ∧ " ++ toStr q ++ ")"
  | p ⋎ q  => "(" ++ toStr p ++ " ∨ "  ++ toStr q ++ ")"
  | p ➝ q => "(" ++ toStr p ++ " ➝ "  ++ toStr q ++ ")"

instance : Repr (Litform α) := ⟨fun t _ => toStr t⟩

instance : ToString (Litform α) := ⟨toStr⟩

end ToString

namespace Meta

variable (F : Q(Type*)) (ls : Q(LogicalConnective $F))

abbrev Lit (F : Q(Type*)) := Litform Q($F)

abbrev toExpr : Lit F → Q($F)
  | atom e  => q($e)
  | ⊤       => q(⊤)
  | ⊥       => q(⊥)
  | p ⋏ q   => q($(toExpr p) ⋏ $(toExpr q))
  | p ⋎ q   => q($(toExpr p) ⋎ $(toExpr q))
  | ~p      => q(~$(toExpr p))
  | p ➝ q  => q($(toExpr p) ➝ $(toExpr q))

partial def denote : Q($F) → MetaM (Lit F)
  | ~q(⊤)        => return ⊤
  | ~q(⊥)        => return ⊥
  | ~q($p ⋏ $q)  => return (←denote p) ⋏ (←denote q)
  | ~q($p ⋎ $q)  => return (←denote p) ⋎ (←denote q)
  | ~q($p ➝ $q) => return (←denote p) ➝ (←denote q)
  | ~q($p ⭤ $q)  => return (←denote p) ⭤ (←denote q)
  | ~q(~$p)      => return ~(←denote p)
  | ~q($e)       => return atom e

instance denotation : Denotation q($F) (Lit F) where
  denote' := denote F ls
  toExpr' := toExpr F ls

abbrev DEq (p q : Lit F) :=
  letI := denotation F ls
  Denotation.DEq F p q

end Meta

end Litform

end LO

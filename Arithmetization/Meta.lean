import Arithmetization.IOpen

open Qq Lean Elab Meta Tactic

namespace LO.FirstOrder

namespace Arith

namespace Meta

variable (M : Q(Type)) {instIh : Q(Inhabited $M)} {instORS : Q(ORingSymbol $M)}

def getIdx {M : Q(Type)} (ts : List (Q($M) × α)) (t : Q($M)) : MetaM (Option α) := do
  let o ← ts.findM? (fun p ↦ Lean.Meta.isDefEq t p.1)
  return o.map Prod.snd

partial def termToTerm (ts : List (Q($M) × α)) : Q($M) → MetaM (Term ℒₒᵣ α)
  | ~q(0)         => return ᵀ“0”
  | ~q(1)         => return ᵀ“1”
  | ~q($t₁ + $t₂) => return ᵀ“!!(←termToTerm ts t₁) + !!(←termToTerm ts t₂)”
  | ~q($t₁ * $t₂) => return ᵀ“!!(←termToTerm ts t₁) * !!(←termToTerm ts t₂)”
  | ~q($t)        => do
    match (←getIdx ts t) with
    | some x => return &x
    | none   => return ᵀ“0”

partial def propToFormula (ts : List (Q(Prop) × α)) : Q(Prop) → MetaM (Formula ℒₒᵣ α)
  | ~q(True) => return “⊤”
  | ~q(False) => return “⊥”
  | ~q(Eq.{1} (α := $M) $t₁ $t₂) => by {  }


end Meta

end Arith

end LO.FirstOrder

import Logic.Predicate.FirstOrder.Basic
import Logic.Predicate.FirstOrder.Principia.Meta

namespace LO

namespace FirstOrder
variable {L : Language.{u}} [L.ORing] [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]

namespace Subformula

namespace Abbrev

def le [L.Lt] : Abbrev L 2 := ⟨“#0 = #1 ∨ #0 < #1”⟩

-- def divides [L.Mul] : Abbrev L 2 := ⟨“∃ #0 * #1 = #2”⟩

end Abbrev

section
variable [L.Lt]

def le : Finitary.{u, v} L 2 := Abbrev.le.toOperator
notation "Op(≤)" => le

lemma le_eq (t₁ t₂ : Subterm L μ n) : le.operator ![t₁, t₂] = “ᵀ!t₁ = ᵀ!t₂ ∨ ᵀ!t₁ < ᵀ!t₂” :=
  by simp[le, Abbrev.le, Abbrev.toOperator]

syntax:45 foterm:45 " ≤ " foterm:0 : foformula

macro_rules
  | `(“ $t₁:foterm ≤ $t₂:foterm ”) => `(Op(≤).operator ![ᵀ“$t₁”, ᵀ“$t₂”])

section delab
open Lean PrettyPrinter Delaborator SubExpr

@[app_unexpander Operator.operator]
def unexpandOpLe : Unexpander
  | `($_ Op(≤) ![ᵀ“$t:foterm”, ᵀ“$u:foterm”]) => `(“ $t:foterm ≤ $u   ”)
  | `($_ Op(≤) ![ᵀ“$t:foterm”, #$y:term    ]) => `(“ $t:foterm ≤ #$y  ”)
  | `($_ Op(≤) ![ᵀ“$t:foterm”, &$y:term    ]) => `(“ $t:foterm ≤ &$y  ”)
  | `($_ Op(≤) ![ᵀ“$t:foterm”, $u          ]) => `(“ $t:foterm ≤ ᵀ!$u ”)
  | `($_ Op(≤) ![#$x:term,     ᵀ“$u:foterm”]) => `(“ #$x       ≤ $u   ”)
  | `($_ Op(≤) ![#$x:term,     #$y:term    ]) => `(“ #$x       ≤ #$y  ”)
  | `($_ Op(≤) ![#$x:term,     &$y:term    ]) => `(“ #$x       ≤ &$y  ”)
  | `($_ Op(≤) ![#$x:term,     $u          ]) => `(“ #$x       ≤ ᵀ!$u ”)
  | `($_ Op(≤) ![&$x:term,     ᵀ“$u:foterm”]) => `(“ &$x       ≤ $u   ”)
  | `($_ Op(≤) ![&$x:term,     #$y:term    ]) => `(“ &$x       ≤ #$y  ”)
  | `($_ Op(≤) ![&$x:term,     &$y:term    ]) => `(“ &$x       ≤ &$y  ”)
  | `($_ Op(≤) ![&$x:term,     $u          ]) => `(“ &$x       ≤ ᵀ!$u ”)
  | `($_ Op(≤) ![$t:term,      ᵀ“$u:foterm”]) => `(“ ᵀ!$t      ≤ $u   ”)
  | `($_ Op(≤) ![$t:term,      #$y:term    ]) => `(“ ᵀ!$t      ≤ #$y  ”)
  | `($_ Op(≤) ![$t:term,      &$y:term    ]) => `(“ ᵀ!$t      ≤ &$y  ”)
  | `($_ Op(≤) ![$t:term,      $u          ]) => `(“ ᵀ!$t      ≤ ᵀ!$u ”)
  | _                                         => throw ()

end delab

end

/-
section 
variable [L.Mul]

def divides : Finitary.{u, v} L 2 := Abbrev.divides.toOperator

lemma divides_eq (t₁ t₂ : Subterm L μ n) :
  divides.operator ![t₁, t₂] = “∃ #0 * ᵀ!(.bShift t₁) = ᵀ!(.bShift t₂)” := by
  simp[divides, Abbrev.divides, Abbrev.toOperator, substs_ex]

end
-/

end Subformula

namespace Order
variable {T : Theory L} [EqTheory T]

def leIffEqOrLt : [] ⟹[T] “∀ ∀ (#0 ≤ #1 ↔ #0 = #1 ∨ #0 < #1)” :=
  by simp[Subformula.le_eq]; exact proofBy { gens _ _; refl }

end Order

end FirstOrder

end LO

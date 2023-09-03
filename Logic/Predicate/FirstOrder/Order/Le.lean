import Logic.Predicate.FirstOrder.Basic.Eq
import Logic.Predicate.FirstOrder.Principia.Meta

namespace LO

namespace FirstOrder
variable {L : Language.{u}} [L.ORing] [∀ k, DecidableEq (L.func k)] [∀ k, DecidableEq (L.rel k)]

namespace SubFormula

namespace Abbrev

def le [L.Lt] : Abbrev L 2 := ⟨“#0 = #1 ∨ #0 < #1”⟩

-- def divides [L.Mul] : Abbrev L 2 := ⟨“∃ #0 * #1 = #2”⟩

end Abbrev

section
variable [L.Lt]

def le : Finitary.{u, v} L 2 := Abbrev.le.toOperator
notation "Op(≤)" => le

lemma le_eq (t₁ t₂ : SubTerm L μ n) : le.operator ![t₁, t₂] = “ᵀ!t₁ = ᵀ!t₂ ∨ ᵀ!t₁ < ᵀ!t₂” :=
  by simp[le, Abbrev.le, Abbrev.toOperator]

syntax:45 subterm:45 " ≤ " subterm:0 : subformula

macro_rules
  | `(“ $t₁:subterm ≤ $t₂:subterm ”) => `(Op(≤).operator ![ᵀ“$t₁”, ᵀ“$t₂”])

section delab
open Lean PrettyPrinter Delaborator SubExpr

@[app_unexpander Operator.operator]
def unexpandOpLe : Unexpander
  | `($_ Op(≤) ![ᵀ“$t:subterm”, ᵀ“$u:subterm”]) => `(“ $t:subterm ≤ $u  ”)
  | `($_ Op(≤) ![ᵀ“$t:subterm”, #$y:term     ]) => `(“ $t:subterm ≤ #$y ”)
  | `($_ Op(≤) ![ᵀ“$t:subterm”, &$y:term     ]) => `(“ $t:subterm ≤ &$y ”)
  | `($_ Op(≤) ![ᵀ“$t:subterm”, $u           ]) => `(“ $t:subterm ≤ ᵀ!$u ”)
  | `($_ Op(≤) ![#$x:term,      ᵀ“$u:subterm”]) => `(“ #$x        ≤ $u  ”)
  | `($_ Op(≤) ![#$x:term,      #$y:term     ]) => `(“ #$x        ≤ #$y ”)
  | `($_ Op(≤) ![#$x:term,      &$y:term     ]) => `(“ #$x        ≤ &$y ”)
  | `($_ Op(≤) ![#$x:term,      $u           ]) => `(“ #$x        ≤ ᵀ!$u ”)
  | `($_ Op(≤) ![&$x:term,      ᵀ“$u:subterm”]) => `(“ &$x        ≤ $u  ”)
  | `($_ Op(≤) ![&$x:term,      #$y:term     ]) => `(“ &$x        ≤ #$y ”)
  | `($_ Op(≤) ![&$x:term,      &$y:term     ]) => `(“ &$x        ≤ &$y ”)
  | `($_ Op(≤) ![&$x:term,      $u           ]) => `(“ &$x        ≤ ᵀ!$u ”)
  | `($_ Op(≤) ![$t:term,       ᵀ“$u:subterm”]) => `(“ ᵀ!$t       ≤ $u  ”)
  | `($_ Op(≤) ![$t:term,       #$y:term     ]) => `(“ ᵀ!$t       ≤ #$y ”)
  | `($_ Op(≤) ![$t:term,       &$y:term     ]) => `(“ ᵀ!$t       ≤ &$y ”)
  | `($_ Op(≤) ![$t:term,       $u           ]) => `(“ ᵀ!$t       ≤ ᵀ!$u ”)
  | _                                           => throw ()

end delab

end

/-
section 
variable [L.Mul]

def divides : Finitary.{u, v} L 2 := Abbrev.divides.toOperator

lemma divides_eq (t₁ t₂ : SubTerm L μ n) :
  divides.operator ![t₁, t₂] = “∃ #0 * ᵀ!(.bShift t₁) = ᵀ!(.bShift t₂)” := by
  simp[divides, Abbrev.divides, Abbrev.toOperator, substs_ex]

end
-/

end SubFormula

namespace Order
variable {T : Theory L} [EqTheory T]

def leIffEqOrLt : [] ⟹[T] “∀ ∀ (#0 ≤ #1 ↔ #0 = #1 ∨ #0 < #1)” :=
  by simp[SubFormula.le_eq]; exact proofBy { generalize; generalize; refl }

end Order

end FirstOrder

end LO

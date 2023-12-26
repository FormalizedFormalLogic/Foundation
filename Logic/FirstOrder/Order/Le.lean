import Logic.FirstOrder.Basic
import Logic.FirstOrder.Completeness.Completeness
--import Logic.FirstOrder.Principia.Meta

namespace LO

namespace FirstOrder

variable {L : Language} [Semiformula.Operator.Eq L] [Semiformula.Operator.LT L]

open Semiformula

def LT.le : Operator L 2 := Semiformula.Operator.Eq.eq.or Semiformula.Operator.LT.lt

lemma le_eq (t₁ t₂ : Semiterm L μ n) : LT.le.operator ![t₁, t₂] = “!!t₁ = !!t₂ ∨ !!t₁ < !!t₂” := by
  simp[Operator.operator, Operator.or, LT.le, ←Rew.hom_comp_app, ←Matrix.fun_eq_vec₂]

namespace Semiformula

syntax:45 foterm:45 " ≤ " foterm:0 : foformula

notation "op(≤)" => Operator.LE.le

macro_rules
  | `(“ $t₁:foterm ≤ $t₂:foterm ”) => `(op(≤).operator ![ᵀ“$t₁”, ᵀ“$t₂”])

section delab
open Lean PrettyPrinter Delaborator SubExpr

@[app_unexpander Operator.operator]
def unexpandOpLe : Unexpander
  | `($_ op(≤) ![ᵀ“$t:foterm”, ᵀ“$u:foterm”]) => `(“ $t:foterm ≤ $u   ”)
  | `($_ op(≤) ![ᵀ“$t:foterm”, #$y:term    ]) => `(“ $t:foterm ≤ #$y  ”)
  | `($_ op(≤) ![ᵀ“$t:foterm”, &$y:term    ]) => `(“ $t:foterm ≤ &$y  ”)
  | `($_ op(≤) ![ᵀ“$t:foterm”, $u          ]) => `(“ $t:foterm ≤ !!$u ”)
  | `($_ op(≤) ![#$x:term,     ᵀ“$u:foterm”]) => `(“ #$x       ≤ $u   ”)
  | `($_ op(≤) ![#$x:term,     #$y:term    ]) => `(“ #$x       ≤ #$y  ”)
  | `($_ op(≤) ![#$x:term,     &$y:term    ]) => `(“ #$x       ≤ &$y  ”)
  | `($_ op(≤) ![#$x:term,     $u          ]) => `(“ #$x       ≤ !!$u ”)
  | `($_ op(≤) ![&$x:term,     ᵀ“$u:foterm”]) => `(“ &$x       ≤ $u   ”)
  | `($_ op(≤) ![&$x:term,     #$y:term    ]) => `(“ &$x       ≤ #$y  ”)
  | `($_ op(≤) ![&$x:term,     &$y:term    ]) => `(“ &$x       ≤ &$y  ”)
  | `($_ op(≤) ![&$x:term,     $u          ]) => `(“ &$x       ≤ !!$u ”)
  | `($_ op(≤) ![$t:term,      ᵀ“$u:foterm”]) => `(“ !!$t      ≤ $u   ”)
  | `($_ op(≤) ![$t:term,      #$y:term    ]) => `(“ !!$t      ≤ #$y  ”)
  | `($_ op(≤) ![$t:term,      &$y:term    ]) => `(“ !!$t      ≤ &$y  ”)
  | `($_ op(≤) ![$t:term,      $u          ]) => `(“ !!$t      ≤ !!$u ”)
  | _                                         => throw ()

end delab

/-
section
variable [L.Mul]

def divides : Finitary.{u, v} L 2 := Abbrev.divides.toOperator

lemma divides_eq (t₁ t₂ : Semiterm L μ n) :
  divides.operator ![t₁, t₂] = “∃ #0 * !!(.bShift t₁) = !!(.bShift t₂)” := by
  simp[divides, Abbrev.divides, Abbrev.toOperator, substs_ex]

end
-/

end Semiformula

namespace Theory.Order

inductive Total (L : Language) [Semiformula.Operator.Eq L] [Semiformula.Operator.LT L] : Sentence L → Prop
  | ltTrans  : Total L “∀ ∀ ∀ (#0 < #1 → #1 < #2 → #0 < #2)”
  | ltIrrefl : Total L “∀ (¬#0 < #0)”
  | ltTri    : Total L “∀ ∀ (#0 < #1 ∨ #0 = #1 ∨#1 < #0)”

end Theory.Order

namespace Order
variable {T : Theory L} [EqTheory T]

noncomputable def leIffEqOrLt : T ⊢ “∀ ∀ (#0 ≤ #1 ↔ #0 = #1 ∨ #0 < #1)” :=
  Complete.complete
    (consequence_iff.mpr $ fun _ _ _ _ => by simp[models_def, Semiformula.Operator.LE.def_of_Eq_of_LT])

class MTotal (M : Type*) [_root_.LT M] :=
  ltTrans : ∀ x y z : M, x < y → y < z → x < z
  ltIrrefl : ∀ x : M, ¬x < x
  ltTri : ∀ x y : M, x < y ∨ x = y ∨ y < x

lemma provOf (σ : Sentence L)
  (H : ∀ (M : Type u)
         [Inhabited M]
         [_root_.LT M]
         [Structure L M]
         [Structure.Eq L M]
         [Structure.LT L M]
         [Theory.Mod M T],
         M ⊧ₘ σ) :
    T ⊨ σ := consequence_iff_eq.mpr fun M _ _ _ hT =>
  letI : Theory.Mod (Structure.Model L M) T := ⟨((Structure.ElementaryEquiv.modelsTheory (Structure.Model.elementaryEquiv L M)).mp hT)⟩
  (Structure.ElementaryEquiv.models (Structure.Model.elementaryEquiv L M)).mpr
    (H (Structure.Model L M))

end Order

end FirstOrder

end LO

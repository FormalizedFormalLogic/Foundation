import Logic.FirstOrder.Basic
import Logic.FirstOrder.Completeness.Completeness
import Logic.FirstOrder.Completeness.Lemmata
--import Logic.FirstOrder.Principia.Meta

namespace LO

namespace FirstOrder

variable {L : Language.{u}} [Semiformula.Operator.Eq L] [Semiformula.Operator.LT L]

open Semiformula

def LT.le : Operator L 2 := Semiformula.Operator.Eq.eq.or Semiformula.Operator.LT.lt

lemma le_eq (t₁ t₂ : Semiterm L μ n) : LT.le.operator ![t₁, t₂] = “!!t₁ = !!t₂ ∨ !!t₁ < !!t₂” := by
  simp [Operator.operator, Operator.or, LT.le, ←Rew.hom_comp_app, ←Matrix.fun_eq_vec₂]

namespace Semiformula
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

namespace Order
variable {T : Theory L} [𝐄𝐐 ≼ T]

noncomputable def leIffEqOrLt : T ⊢! “∀ x y, x ≤ y ↔ x = y ∨ x < y” :=
  complete
    (consequence_iff.mpr $ fun _ _ _ _ => by simp[models_def, Semiformula.Operator.LE.def_of_Eq_of_LT])

lemma provOf (σ : Sentence L)
  (H : ∀ (M : Type (max u w))
         [Nonempty M] [LT M]
         [Structure L M] [Structure.Eq L M] [Structure.LT L M]
         [M ⊧ₘ* T],
         M ⊧ₘ σ) :
    T ⊨ σ := consequence_iff_consequence.{u, w}.mp <| consequence_iff_eq.mpr fun M _ _ _ hT =>
  letI : (Structure.Model L M) ⊧ₘ* T :=
    ((Structure.ElementaryEquiv.modelsTheory (Structure.Model.elementaryEquiv L M)).mp hT)
  (Structure.ElementaryEquiv.models (Structure.Model.elementaryEquiv L M)).mpr (H (Structure.Model L M))

end Order

end FirstOrder

end LO

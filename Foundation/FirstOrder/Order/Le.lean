module

public import Foundation.FirstOrder.Completeness.CanonicalModel
public import Foundation.FirstOrder.Completeness.CountableSublanguage
public import Foundation.FirstOrder.Completeness.CounterModel

@[expose] public section
namespace LO

namespace FirstOrder

variable {L : Language.{u}} [Semiformula.Operator.Eq L] [Semiformula.Operator.LT L]

open Semiformula

def LT.le : Operator L 2 := Semiformula.Operator.Eq.eq.or Semiformula.Operator.LT.lt

lemma le_eq (t₁ t₂ : Semiterm L μ n) : LT.le.operator ![t₁, t₂] = “!!t₁ = !!t₂ ∨ !!t₁ < !!t₂” := by
  simp [Operator.operator, Operator.or, LT.le, ←TransitiveRewriting.comp_app]

namespace Order
variable {T : Theory L} [𝗘𝗤 L ⪯ T]

noncomputable def leIffEqOrLt : T ⊢ “∀ x y, x ≤ y ↔ x = y ∨ x < y” :=
  Theory.Proof.small_complete
    <| consequence_iff.mpr fun _ ↦ by simp [models_iff, Semiformula.Operator.LE.def_of_Eq_of_LT]

lemma complete (φ : Sentence L)
  (H : ∀ (M : Type (max u w))
      [Nonempty M] [LT M]
      [Structure L M] [Structure.Eq L M] [Structure.LT L M]
      [M↓[L] ⊧* T],
      M↓[L] ⊧ φ) :
    T ⊢ φ := Theory.Proof.complete <| consequence_iff_eq.mpr fun M _ _ _ hT ↦
  letI : (Structure.Model L M)↓[L] ⊧* T := Structure.ElementaryEquiv.modelsTheory.mp hT
  Structure.ElementaryEquiv.models.mpr (H (Structure.Model L M))

end Order

end FirstOrder

end LO

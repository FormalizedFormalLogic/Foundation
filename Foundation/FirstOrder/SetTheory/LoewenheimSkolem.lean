import Foundation.FirstOrder.SetTheory.Basic
import Foundation.FirstOrder.SetTheory.StandardModel
import Foundation.FirstOrder.LoewenheimSkolem

/-!
# Downward Löwenheim-Skolem theorem for models of set theory
-/

namespace LO.FirstOrder.SetTheory

variable (M : Type*) [SetStructure M] [Nonempty M]

instance : Structure.Collapse ℒₛₑₜ M ⊧ₘ* (𝗘𝗤 : Theory ℒₛₑₜ) :=
   Structure.ElementaryEquiv.modelsTheory.mp (inferInstanceAs (M ⊧ₘ* (𝗘𝗤 : Theory ℒₛₑₜ)))

/-- A function returns "collapsed", but elemetary equivalent model -/
abbrev Collapse (M : Type*) [SetStructure M] [Nonempty M] : Type _ := QuotNormalize (Structure.Collapse ℒₛₑₜ M)

namespace Collapse

instance elementary_equiv : Collapse M ≡ₑ[ℒₛₑₜ] M :=
  have h₁ : Collapse M ≡ₑ[ℒₛₑₜ] Structure.Collapse ℒₛₑₜ M := QuotNormalize.elementary_equiv
  have h₂ : Structure.Collapse ℒₛₑₜ M ≡ₑ[ℒₛₑₜ] M := Structure.Collapse.equiv ℒₛₑₜ M
  h₁.trans h₂

open Cardinal

@[simp] lemma le_aleph0  : #(Collapse M) ≤ ℵ₀ := by
    simpa using QuotNormalize.card_le (Structure.Collapse ℒₛₑₜ M)

instance countable : Countable (Collapse M) :=
  QuotNormalize.countable_of_countable (Structure.Collapse ℒₛₑₜ M)

end Collapse

/-- Collapsed ZFSet; a countable model of ZFC. -/
abbrev CollapsedZFSet.{u} : Type := Collapse ZFSet.{u}

instance CollapsedZFSet.elementary_equiv : CollapsedZFSet.{u} ≡ₑ[ℒₛₑₜ] ZFSet.{u} := inferInstance

instance CollapsedZFSet.countable : Countable CollapsedZFSet.{u} := inferInstance

instance CollapsedZFSet.modelsZFC : CollapsedZFSet.{u} ⊧ₘ* 𝗭𝗙𝗖 :=
  Structure.ElementaryEquiv.modelsTheory' CollapsedZFSet.{u} ZFSet.{u} _

end LO.FirstOrder.SetTheory

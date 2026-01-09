module
import Foundation.FirstOrder.Bootstrapping.DerivabilityCondition
import Foundation.FirstOrder.Bootstrapping.Consistency
import Foundation.FirstOrder.Bootstrapping.RosserProvability

/-!
# Gödel's second incompleteness theorem for arithmetic theories stronger than $\mathsf{I}\Sigma_1$
-/

namespace LO.FirstOrder.Arithmetic

open LO.Entailment ProvabilityLogic

variable (T : Theory ℒₒᵣ) [T.Δ₁] [𝗜𝚺₁ ⪯ T]

/-- Gödel's second incompleteness theorem -/
theorem consistent_unprovable [Consistent T] :
    T ⊬ ↑T.consistent :=
  T.standardProvability.con_unprovable

theorem inconsistent_unprovable [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] :
    T ⊬ ∼↑T.consistent :=
  T.standardProvability.con_unrefutable

/-- The consistency statement is independent. -/
theorem inconsistent_independent [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] :
    Independent T ↑T.consistent :=
  T.standardProvability.con_independent

instance [Consistent T] : T ⪱ T + T.Con :=
  StrictlyWeakerThan.of_unprovable_provable (φ := ↑T.consistent)
    (consistent_unprovable T)
    (Entailment.by_axm _ (by simp [Theory.add_def]))

instance [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] : T ⪱ T + T.Incon :=
  StrictlyWeakerThan.of_unprovable_provable (φ := ∼↑T.consistent)
    (inconsistent_unprovable T)
    (Entailment.by_axm _ (by simp [Theory.add_def]))

/-- Gödel-Rosser incompleteness theorem -/
theorem incomplete' [Consistent T] : Entailment.Incomplete T :=
  T.rosserProvability.rosser_first_incompleteness

end LO.FirstOrder.Arithmetic

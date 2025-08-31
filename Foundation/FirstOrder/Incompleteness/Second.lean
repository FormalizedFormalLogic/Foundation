import Foundation.FirstOrder.Internal.DerivabilityCondition
import Foundation.FirstOrder.Internal.Consistency
import Foundation.FirstOrder.Internal.RosserProvability

/-!
# Gödel's second incompleteness theorem for arithmetic theories stronger than $\mathsf{I}\Sigma_1$
-/

namespace LO.FirstOrder.Arithmetic

open LO.Entailment ProvabilityLogic

variable (T : Theory ℒₒᵣ) [T.Δ₁] [𝐈𝚺₁ ⪯ T]

/-- Gödel's second incompleteness theorem -/
theorem consistent_unprovable [Consistent T] :
    T ⊬. T.consistent :=
  T.standardProvability.con_unprovable

theorem inconsistent_unprovable [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] :
    T ⊬. ∼T.consistent :=
  T.standardProvability.con_unrefutable

theorem inconsistent_independent [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] :
    Independent (T : Axiom ℒₒᵣ) (T.consistent : Sentence ℒₒᵣ) :=
  T.standardProvability.con_independent

instance [Consistent T] : T ⪱ T + T.Con :=
  StrictlyWeakerThan.of_unprovable_provable (φ := ↑T.consistent)
    ((Axiom.unprovable_iff (T := T)).mp (consistent_unprovable T))
    (Entailment.by_axm _ (by simp [Theory.add_def]))

instance [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] : T ⪱ T + T.Incon :=
  StrictlyWeakerThan.of_unprovable_provable (φ := ∼↑T.consistent)
    (by simpa using (Axiom.unprovable_iff (T := T)).mp (inconsistent_unprovable T))
    (Entailment.by_axm _ (by simp [Theory.add_def]))

/-- Gödel-Rosser incompleteness theorem -/
theorem incomplete' [Consistent T] : Entailment.Incomplete (T : Axiom ℒₒᵣ) :=
  T.rosserProvability.rosser_first_incompleteness

end LO.FirstOrder.Arithmetic

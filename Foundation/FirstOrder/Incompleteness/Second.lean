import Foundation.FirstOrder.Internal.DerivabilityCondition
import Foundation.FirstOrder.Internal.Consistency
import Foundation.FirstOrder.Internal.RosserProvability

/-!
# Gödel's second incompleteness theorem for arithmetic theories stronger than $\mathsf{I}\Sigma_1$
-/

namespace LO.FirstOrder.Arithmetic

open LO.Entailment ProvabilityLogic

variable (T : ArithmeticTheory) [T.Δ₁] [𝐈𝚺₁ ⪯ T]

/-- Gödel's second incompleteness theorem -/
theorem consistent_unprovable [Consistent T] :
    T ⊬. T.consistent :=
  T.standardPr.con_unprovable

theorem inconsistent_unprovable [T.SoundOnHierarchy 𝚺 1] :
    T ⊬. ∼T.consistent :=
  T.standardPr.con_unrefutable

theorem inconsistent_independent [T.SoundOnHierarchy 𝚺 1] :
    Independent (T : Axiom ℒₒᵣ) (T.consistent : Sentence ℒₒᵣ) :=
  T.standardPr.con_independent

instance [Consistent T] : T ⪱ T + T.Con :=
  StrictlyWeakerThan.of_unprovable_provable (φ := ↑T.consistent)
    ((Axiom.unprovable_iff (T := T)).mp (consistent_unprovable T))
    (Entailment.by_axm _ (by simp [Theory.add_def]))

instance [T.SoundOnHierarchy 𝚺 1] : T ⪱ T + T.Incon :=
  StrictlyWeakerThan.of_unprovable_provable (φ := ∼↑T.consistent)
    (by simpa using (Axiom.unprovable_iff (T := T)).mp (inconsistent_unprovable T))
    (Entailment.by_axm _ (by simp [Theory.add_def]))

/-- Gödel-Rosser incompleteness theorem -/
theorem incomplete' [Consistent T] : ¬Entailment.Complete (T : Axiom ℒₒᵣ) :=
  T.rosserPr.rosser_first_incompleteness

end LO.FirstOrder.Arithmetic

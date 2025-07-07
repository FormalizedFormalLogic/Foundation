import Foundation.FirstOrder.Incompleteness.StandardProvability
import Foundation.FirstOrder.Incompleteness.ConsistencyPredicate

/-!
# Gödel's second incompleteness theorem for arithmetic theories stronger than $\mathsf{I}\Sigma_1$
-/

namespace LO.FirstOrder.Arith

open LO.Entailment ProvabilityLogic

variable (T : ArithmeticTheory) [𝐈𝚺₁ ⪯ T] [T.Delta1Definable]

/-- Gödel's second incompleteness theorem-/
theorem goedel_second_incompleteness [Consistent T] :
    T ⊬. T.isConsistent :=
  T.standardPr.unprovable_consistency

theorem inconsistent_unprovable [T.Sigma1Sound] :
    T ⊬. ∼T.isConsistent :=
  T.standardPr.unrefutable_consistency

theorem inconsistent_independent [T.Sigma1Sound] :
    Independent (T : Axiom ℒₒᵣ) (T.isConsistent : Sentence ℒₒᵣ) :=
  T.standardPr.consistency_independent

instance [Consistent T] : T ⪱ T + T.Con :=
  StrictlyWeakerThan.of_unprovable_provable (φ := ↑T.isConsistent)
    ((Axiom.unprovable_iff (T := T)).mp (goedel_second_incompleteness T))
    (Entailment.by_axm _ (by simp))

instance [T.Sigma1Sound] : T ⪱ T + T.Incon :=
  StrictlyWeakerThan.of_unprovable_provable (φ := ∼↑T.isConsistent)
    (by simpa using (Axiom.unprovable_iff (T := T)).mp (inconsistent_unprovable T))
    (Entailment.by_axm _ (by simp))

end LO.FirstOrder.Arith

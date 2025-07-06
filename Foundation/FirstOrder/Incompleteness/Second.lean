import Foundation.FirstOrder.Incompleteness.StandardProvability
import Foundation.FirstOrder.Incompleteness.ConsistencyPredicate

/-!
# Gödel's second incompleteness theorem for arithmetic theories stronger than $\mathsf{I}\Sigma_1$
-/

namespace LO.ISigma1

open FirstOrder Entailment ProvabilityLogic

variable (T : ArithmeticTheory) [𝐈𝚺₁ ⪯ T] [T.Delta1Definable]

/-- Gödel's second incompleteness theorem-/
theorem goedel_second_incompleteness [Consistent T] :
    T ⊬. T.isConsistent :=
  T.standardPr.unprovable_consistency

theorem inconsistent_unprovable [T.Sigma1Sound] :
    T ⊬. ∼T.isConsistent :=
  have : 𝐑₀ ⪯ T := WeakerThan.trans (inferInstanceAs (𝐑₀ ⪯ 𝐈𝚺₁)) inferInstance
  T.standardPr.unrefutable_consistency

theorem inconsistent_independent [T.Sigma1Sound] :
    Independent (T : Axiom ℒₒᵣ) (T.isConsistent : Sentence ℒₒᵣ) :=
  have : 𝐑₀ ⪯ T := WeakerThan.trans (inferInstanceAs (𝐑₀ ⪯ 𝐈𝚺₁)) inferInstance
  T.standardPr.consistency_independent

abbrev _root_.LO.FirstOrder.ArithmeticTheory.AddSelfConsistency : ArithmeticTheory := T + {↑T.isConsistent}

abbrev _root_.LO.FirstOrder.ArithmeticTheory.AddSelfInconsistency : ArithmeticTheory := T + {∼↑T.isConsistent}

instance [Consistent T] : T ⪱ T.AddSelfConsistency :=
  StrictlyWeakerThan.of_unprovable_provable (φ := ↑T.isConsistent)
    ((Axiom.unprovable_iff (T := T)).mp (goedel_second_incompleteness T))
    (Entailment.by_axm _ (by simp))

instance [ℕ ⊧ₘ* T] : ℕ ⊧ₘ* T.AddSelfConsistency := by
  have : 𝐑₀ ⪯ T := WeakerThan.trans (inferInstanceAs (𝐑₀ ⪯ 𝐈𝚺₁)) inferInstance
  have : Consistent T := ArithmeticTheory.consistent_of_sound T (Eq ⊥) rfl
  simp [models_iff, *]

instance [T.Sigma1Sound] : T ⪱ T.AddSelfInconsistency :=
  StrictlyWeakerThan.of_unprovable_provable (φ := ∼↑T.isConsistent)
    (by simpa using (Axiom.unprovable_iff (T := T)).mp (inconsistent_unprovable T))
    (Entailment.by_axm _ (by simp))

end LO.ISigma1

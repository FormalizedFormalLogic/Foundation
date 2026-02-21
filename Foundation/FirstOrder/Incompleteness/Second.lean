module

public import Foundation.FirstOrder.Bootstrapping.Consistency
public import Foundation.FirstOrder.Incompleteness.RosserProvability

@[expose] public section
/-!
# Gödel's second incompleteness theorem for arithmetic theories stronger than $\mathsf{I}\Sigma_1$
-/

namespace LO.FirstOrder.Arithmetic

open LO.Entailment ProvabilityAbstraction

variable (T : Theory ℒₒᵣ) [T.Δ₁] [𝗜𝚺₁ ⪯ T]

/-- Gödel's second incompleteness theorem -/
theorem consistent_unprovable [Consistent T] : T ⊬ ↑T.consistent :=
  ProvabilityAbstraction.con_unprovable (𝔅 := T.standardProvability)

theorem inconsistent_unprovable [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] : T ⊬ ∼↑T.consistent :=
  ProvabilityAbstraction.con_unrefutable (𝔅 := T.standardProvability)

/-- The consistency statement is independent. -/
theorem inconsistent_independent [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] : Independent T ↑T.consistent :=
  ProvabilityAbstraction.con_independent (𝔅 := T.standardProvability)

instance [Consistent T] : T ⪱ T + T.Con :=
  StrictlyWeakerThan.of_unprovable_provable (φ := ↑T.consistent)
    (consistent_unprovable T)
    (Entailment.by_axm _ (by simp [Theory.add_def]))

instance [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] : T ⪱ T + T.Incon :=
  StrictlyWeakerThan.of_unprovable_provable (φ := ∼↑T.consistent)
    (inconsistent_unprovable T)
    (Entailment.by_axm _ (by simp [Theory.add_def]))

end LO.FirstOrder.Arithmetic

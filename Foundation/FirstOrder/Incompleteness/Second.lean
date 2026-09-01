module

public import Foundation.FirstOrder.Incompleteness.Consistency
public import Foundation.FirstOrder.Incompleteness.RosserProvability
public import Foundation.FirstOrder.Bootstrapping.Syntax.CraigTrick

@[expose] public section
/-!
# Gödel's second incompleteness theorem for arithmetic theories stronger than $\mathsf{I}\Sigma_1$
-/

namespace LO.FirstOrder.Arithmetic

open LO.Entailment ProvabilityAbstraction

variable (T : ArithmeticTheory) [T.Δ₁] [𝗜𝚺₁ ⪯ T]

/-- Gödel's second incompleteness theorem -/
theorem consistent_unprovable [Consistent T] : T ⊬ T.consistent.val :=
  ProvabilityAbstraction.con_unprovable (𝔅 := T.standardProvability)

/-- Gödel's second incompleteness theorem for r.e. theories -/
theorem craig_consistent_unprovable_of_re (T : ArithmeticTheory) [T.RE] [𝗜𝚺₁ ⪯ T]
    [Consistent T] : T ⊬ T.craig.consistent.val := by
  let craig_weakerThan : 𝗜𝚺₁ ⪯ T.craig :=
    WeakerThan.trans (𝓣 := T) inferInstance (Theory.craig.original_weakerThan (T := T))
  intro h;
  exact @consistent_unprovable T.craig inferInstance craig_weakerThan inferInstance
    (WeakerThan.pbl h)

theorem inconsistent_unprovable [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] : T ⊬ ∼T.consistent.val :=
  ProvabilityAbstraction.con_unrefutable (𝔅 := T.standardProvability)

/-- The consistency statement is independent. -/
theorem inconsistent_independent [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] : Independent T T.consistent.val :=
  ProvabilityAbstraction.con_independent (𝔅 := T.standardProvability)

instance [Consistent T] : T ⪱ T ∪ T.Con :=
  StrictlyWeakerThan.of_unprovable_provable (φ := T.consistent)
    (consistent_unprovable T)
    (Entailment.by_axm (by simp))

instance [ArithmeticTheory.SoundOnHierarchy T 𝚺 1] : T ⪱ T ∪ T.Incon :=
  StrictlyWeakerThan.of_unprovable_provable (φ := ∼T.consistent)
    (inconsistent_unprovable T)
    (Entailment.by_axm (by simp))

end LO.FirstOrder.Arithmetic

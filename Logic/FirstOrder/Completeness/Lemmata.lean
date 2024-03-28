import Logic.FirstOrder.Completeness.Completeness

namespace LO.FirstOrder

namespace Theory.Mod

variable (M : Type _) [Nonempty M] [Structure L M] (T U V : Theory L)

lemma of_provably_subtheory (_ : T ≾ U) [U.Mod M] : T.Mod M :=
  of_subtheory M (Semantics.ofSystemSubtheory T U)

lemma of_provably_subtheory' [T ≾ U] [U.Mod M] : T.Mod M := of_provably_subtheory M T U inferInstance

lemma of_add_left [(T + U).Mod M] : T.Mod M := of_ss M (show T ⊆ T + U from by simp [Theory.add_def])

lemma of_add_right [(T + U).Mod M] : U.Mod M := of_ss M (show U ⊆ T + U from by simp [Theory.add_def])

lemma of_add_left_left [(T + U + V).Mod M] : T.Mod M := @of_add_left _ M _ _ T U (of_add_left M (T + U) V)

lemma of_add_left_right [(T + U + V).Mod M] : U.Mod M := @of_add_right _ M _ _ T U (of_add_left M (T + U) V)

end Theory.Mod

end LO.FirstOrder

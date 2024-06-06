import Logic.FirstOrder.Completeness.Completeness

namespace LO.FirstOrder

namespace ModelsTheory

variable {L : Language.{u}} (M : Type w) [Nonempty M] [Structure L M] (T U V : Theory L)

lemma of_provably_subtheory (_ : T ≼ U) (h : M ⊧ₘ* U) : M ⊧ₘ* T := ⟨by
  intro p hp
  have : U ⊢ p := System.Subtheory.prf (System.byAxm hp)
  exact consequence_iff'.{u, w}.mp (sound! ⟨this⟩) M⟩

lemma of_provably_subtheory' [T ≼ U] [M ⊧ₘ* U] : M ⊧ₘ* T := of_provably_subtheory M T U inferInstance inferInstance

lemma of_add_left [M ⊧ₘ* T + U] : M ⊧ₘ* T := of_ss inferInstance (show T ⊆ T + U from by simp [Theory.add_def])

lemma of_add_right [M ⊧ₘ* T + U] : M ⊧ₘ* U := of_ss inferInstance (show U ⊆ T + U from by simp [Theory.add_def])

lemma of_add_left_left [M ⊧ₘ* T + U + V] : M ⊧ₘ* T := @of_add_left _ M _ _ T U (of_add_left M (T + U) V)

lemma of_add_left_right [M ⊧ₘ* T + U + V] : M ⊧ₘ* U := @of_add_right _ M _ _ T U (of_add_left M (T + U) V)

end ModelsTheory

theorem completeness_iff_with_eq {L : Language} [L.Eq] {T : Theory L} {σ : Sentence L} : T⁼ ⊨ σ ↔ T⁼ ⊢! σ := complete_iff

end LO.FirstOrder

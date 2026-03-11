module

public import Foundation.Propositional.Kripke3.Axiom.WLEM

@[expose] public section

namespace LO.Propositional

open LO.Entailment
open SaturatedConsistentTableau
open KripkeModel

namespace KC

variable [Consistent (Propositional.KC)]

theorem provable_of_forall_convergent_model_validates
  : (∀ {κ : Type 0}, [Nonempty κ] → ∀ M : KripkeModel κ ℕ, [M.Intuitionistic] → [IsPiecewiseStronglyConvergent M.rel] → M ⊧ φ) → (Propositional.KC) ⊢ φ
  := fun h ↦ canonicalKripkeModel.iff_validates_provable.mp $ h _

lemma exists_convergent_model_of_unprovable (h : (Propositional.KC) ⊬ φ)
  : ∃ κ : Type 0, ∃ _ : Nonempty κ, ∃ M : KripkeModel κ ℕ, ∃ _ : M.Intuitionistic, ∃ _ : IsPiecewiseStronglyConvergent M.rel, ∃ w : M.world, w ⊮ φ := by
  contrapose! h;
  apply provable_of_forall_convergent_model_validates;
  apply h;

end KC


end LO.Propositional


end

module

public import Foundation.Propositional.Kripke3.Axiom.Dummett

@[expose] public section

namespace LO.Propositional

open LO.Entailment
open SaturatedConsistentTableau
open KripkeModel

namespace LC

variable [Consistent (Propositional.LC)]

theorem provable_of_forall_connected_model_validates
  : (∀ {κ : Type 0}, [Nonempty κ] → ∀ M : KripkeModel κ ℕ, [M.Intuitionistic] → [IsPiecewiseStronglyConnected M.rel] → M ⊧ φ) → (Propositional.LC) ⊢ φ
  := fun h ↦ canonicalKripkeModel.iff_validates_provable.mp $ h _

lemma exists_connected_model_of_unprovable (h : (Propositional.LC) ⊬ φ)
  : ∃ κ : Type 0, ∃ _ : Nonempty κ, ∃ M : KripkeModel κ ℕ, ∃ _ : M.Intuitionistic, ∃ _ : IsPiecewiseStronglyConnected M.rel, ∃ w : M.world, w ⊮ φ := by
  contrapose! h;
  apply provable_of_forall_connected_model_validates;
  apply h;

end LC


end LO.Propositional


end

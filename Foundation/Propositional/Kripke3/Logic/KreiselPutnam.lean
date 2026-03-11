module

public import Foundation.Propositional.Kripke3.Axiom.KreiselPutnam

@[expose] public section

namespace LO.Propositional

open LO.Entailment
open SaturatedConsistentTableau
open KripkeModel

namespace KreiselPutnam

variable [Consistent (Propositional.KreiselPutnam)]

theorem provable_of_forall_kreisel_putnam_model_validates
  : (∀ {κ : Type 0}, [Nonempty κ] → ∀ M : KripkeModel κ ℕ, [M.KreiselPutnam] → M ⊧ φ) → (Propositional.KreiselPutnam) ⊢ φ
  := fun h ↦ canonicalKripkeModel.iff_validates_provable.mp $ h _

lemma exists_kreisel_putnam_model_of_unprovable (h : (Propositional.KreiselPutnam) ⊬ φ)
  : ∃ κ : Type 0, ∃ _ : Nonempty κ, ∃ M : KripkeModel κ ℕ, ∃ _ : M.KreiselPutnam, ∃ w : M.world, w ⊮ φ := by
  contrapose! h;
  apply provable_of_forall_kreisel_putnam_model_validates;
  apply h;

end KreiselPutnam


end LO.Propositional


end

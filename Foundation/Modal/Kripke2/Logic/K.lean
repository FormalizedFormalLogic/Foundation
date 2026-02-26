module

public import Foundation.Modal.Kripke2.Hilbert
public import Foundation.Modal.Kripke2.Completeness

@[expose] public section

namespace LO.Modal

variable {φ : Formula ℕ}

namespace K

theorem kripke_sound : Modal.K ⊢ φ → (∀ M : KripkeModel ℕ, M ⊧ φ) := by
  intro h M;
  apply Hilbert.Normal.valid_of_provable M ?_ h;
  rintro V _ ⟨_, rfl⟩;
  apply KripkeModel.models_axiomK;

instance : Entailment.Consistent Modal.K := by
  apply Hilbert.Normal.consistent_of_valid_model (M := ⟨Fin 1, λ _ _ => True, λ _ _ => True⟩);
  rintro V _ ⟨_, rfl⟩;
  apply KripkeModel.models_axiomK;

theorem kripke_complete : (∀ M : KripkeModel.{0, 0} _, M ⊧ φ) → Modal.K ⊢ φ := by
  intro h;
  apply canonicalKripkeModel.iff_valid_provable.mp;
  apply h;

end K


end LO.Modal

end

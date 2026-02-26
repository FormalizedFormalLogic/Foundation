module

public import Foundation.Modal.Kripke2.Hilbert
public import Foundation.Modal.Kripke2.Completeness

@[expose] public section

namespace LO.Modal

variable {α : Type u} {φ : Formula α}

namespace K

theorem kripke_sound : Modal.K _ ⊢ φ → (∀ {κ}, [Nonempty κ] → ∀ F : Rel κ κ, ∀ V, (⟨F, V⟩ : KripkeModel κ α) ⊧ φ)
  := by
  intro h κ _ F;
  apply Hilbert.Normal.valid_of_provable2 F ?_ h;
  rintro V _ ⟨_, _, rfl⟩;
  exact KripkeModel.models_axiomK;

theorem kripke_sound' : Modal.K _ ⊢ φ → (∀ {κ}, [Nonempty κ] → ∀ M : KripkeModel κ α, M ⊧ φ)
  := fun h {κ} [Nonempty κ] M ↦ kripke_sound h M.rel M.val

instance : Entailment.Consistent (Modal.K α) := by
  apply Hilbert.Normal.consistent_of_valid_model' (κ := Fin 1) (λ _ _ => True);
  rintro V _ ⟨_, _, rfl⟩;
  apply KripkeModel.models_axiomK;

variable [DecidableEq α] [Encodable α] [Entailment.K (Modal.K α)]
theorem kripke_complete : (∀ {κ : Type u}, [Nonempty κ] → ∀ M : KripkeModel κ α, M ⊧ φ) → Modal.K α ⊢ φ
  := fun h ↦ canonicalKripkeModel.iff_valid_provable.mp $ h _

theorem iff_provable_valid_all_kripkeModel : Modal.K α ⊢ φ ↔ (∀ {κ : Type u}, [Nonempty κ] → ∀ M : KripkeModel κ α, M ⊧ φ) := by
  constructor;
  . apply kripke_sound';
  . apply kripke_complete;

end K


end LO.Modal

end

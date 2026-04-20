module

public import Foundation.Modal.Kripke2.Hilbert
public import Foundation.Modal.Kripke2.Completeness

@[expose] public section

namespace LO.Modal

variable {α : Type u} {φ : Formula α}

namespace K

theorem forall_frame_validates_of_provable (h : Modal.K' α ⊢ φ)
  : ∀ {κ}, [Nonempty κ] → ∀ F, ∀ V, (⟨F, V⟩ : KripkeModel κ α) ⊧ φ := by
  intro κ _ K;
  apply Hilbert.Normal2.valid_of_provable K ?_ h;
  rintro V;
  constructor;
  intro _ h;
  rcases (by simpa [Hilbert.Normal2.buildAxioms] using h) with ⟨_, _, rfl⟩; grind;

theorem forall_model_validates_of_provable (h : Modal.K' α ⊢ φ)
  : ∀ {κ}, [Nonempty κ] → ∀ M : KripkeModel κ α, M ⊧ φ
  := fun M ↦ forall_frame_validates_of_provable h M.frame M.val

instance : Entailment.Consistent (Modal.K' α) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  by_contra! hC;
  apply KripkeModel.validates_falsum $
    forall_frame_validates_of_provable hC (λ (_ : Fin 1) _ => True) (λ _ _ => True);

instance : Entailment.K (Modal.K' α) where

variable [DecidableEq α] [Encodable α]

theorem provable_of_forall_model_validates : (∀ {κ : Type u}, [Nonempty κ] → ∀ M : KripkeModel κ α, M ⊧ φ) → Modal.K' _ ⊢ φ
  := fun h ↦ canonicalKripkeModel.iff_valid_provable.mp $ h _

theorem iff_provable_valid_all_kripkeModel : Modal.K' α ⊢ φ ↔ (∀ κ : Type u, [Nonempty κ] → ∀ M : KripkeModel κ α, M ⊧ φ) := by
  constructor;
  . exact forall_model_validates_of_provable;
  . exact provable_of_forall_model_validates;

end K


end LO.Modal

end

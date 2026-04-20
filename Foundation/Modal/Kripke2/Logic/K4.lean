module

public import Foundation.Modal.Kripke2.Logic.K
public import Foundation.Modal.Kripke2.Axiom.Geach

@[expose] public section

namespace LO.Modal

variable {α : Type u} {κ : Type*} [Nonempty κ] {φ : Formula α}

namespace K4'

instance : Entailment.K4 (Modal.K4' α) where

theorem forall_transitive_frame_validates_of_provable (h : Modal.K4' α ⊢ φ)
  : ∀ {κ : Type*}, [Nonempty κ] → ∀ K, [IsTrans _ K] → ∀ V, (⟨K, V⟩ : KripkeModel κ α) ⊧ φ := by
  intro κ _ F _;
  apply Hilbert.Normal2.valid_of_provable F ?_ h;
  rintro V;
  constructor;
  intro _ hφ;
  rcases (by simpa [Hilbert.Normal2.buildAxioms] using hφ) with (⟨_, rfl⟩ | (⟨_, _, rfl⟩)) <;> grind;

lemma forall_transitive_frame_validates_of_provable' (h : Modal.K4' α ⊢ φ)
  : ∀ {κ : Type*}, [Nonempty κ] → ∀ K, (Transitive K) → ∀ V, (⟨K, V⟩ : KripkeModel κ α) ⊧ φ
  := by
  rintro _ _ F F_trans;
  have : IsTrans _ F := by constructor; tauto;
  exact forall_transitive_frame_validates_of_provable h F;

theorem forall_transitive_model_validates_of_provable (h : Modal.K4' α ⊢ φ)
  : ∀ {κ}, [Nonempty κ] → ∀ M : KripkeModel κ α, [IsTrans _ M.rel] → M ⊧ φ
  := fun M ↦ forall_transitive_frame_validates_of_provable h M.frame M.val


instance : Entailment.Consistent (Modal.K4' α) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  by_contra! hC;
  apply KripkeModel.validates_falsum $
    forall_transitive_frame_validates_of_provable' hC (λ (_ : Fin 1) _ => True) (by tauto) (λ _ _ => True);

variable [DecidableEq α] [Encodable α]

theorem provable_of_forall_transitive_model_validate
  (h : ∀ {κ : Type u}, [Nonempty κ] → ∀ M : KripkeModel κ α, [IsTrans _ M.rel] → M ⊧ φ)
  : Modal.K4' α ⊢ φ
  := canonicalKripkeModel.iff_valid_provable.mp $ h _

theorem iff_provable_provable_forall_transitive_model_validate
  : Modal.K4' α ⊢ φ ↔ (∀ {κ : Type u}, [Nonempty κ] → ∀ M : KripkeModel κ α, [IsTrans _ M.rel] → M ⊧ φ)
  := by
  constructor;
  . apply forall_transitive_model_validates_of_provable;
  . apply provable_of_forall_transitive_model_validate;

end K4'


end LO.Modal

end

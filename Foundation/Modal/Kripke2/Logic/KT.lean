module

public import Foundation.Modal.Kripke2.Logic.K
public import Foundation.Modal.Kripke2.Axiom.Geach

@[expose] public section

namespace LO.Modal

variable {α : Type u} {φ : Formula α}

namespace KT'

instance : Entailment.KT (Modal.KT' α) where

theorem forall_reflexive_frame_validates_of_provable (h : Modal.KT' α ⊢ φ)
  : ∀ {κ : Type*}, [Nonempty κ] → ∀ K, [Std.Refl K] → ∀ V, (⟨K, V⟩ : KripkeModel κ α) ⊧ φ := by
  intro κ _ F _;
  apply Hilbert.Normal2.valid_of_provable F ?_ h;
  rintro V;
  constructor;
  intro _ hφ;
  rcases (by simpa [Hilbert.Normal2.buildAxioms] using hφ) with ((⟨_, _, rfl⟩ | ⟨_, rfl⟩)) <;> grind;

lemma forall_reflexive_frame_validates_of_provable' (h : Modal.KT' α ⊢ φ)
  : ∀ {κ : Type*}, [Nonempty κ] → ∀ K, (Reflexive K) → ∀ V, (⟨K, V⟩ : KripkeModel κ α) ⊧ φ
  := by
  rintro _ _ F F_reflexive;
  have : Std.Refl F := by constructor; tauto;
  exact forall_reflexive_frame_validates_of_provable h F;

theorem forall_reflexive_model_validates_of_provable (h : Modal.KT' α ⊢ φ)
  : ∀ {κ}, [Nonempty κ] → ∀ M : KripkeModel κ α, [Std.Refl M.rel] → M ⊧ φ
  := fun M ↦ forall_reflexive_frame_validates_of_provable h M.frame M.val


instance : Entailment.Consistent (Modal.KT' α) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  by_contra! hC;
  apply KripkeModel.validates_falsum $
    forall_reflexive_frame_validates_of_provable' hC (λ (_ : Fin 1) _ => True) (by tauto) (λ _ _ => True);

variable [DecidableEq α] [Encodable α]

theorem provable_of_forall_reflexive_model_validate
  (h : ∀ {κ : Type u}, [Nonempty κ] → ∀ M : KripkeModel κ α, [Std.Refl M.rel] → M ⊧ φ)
  : Modal.KT' α ⊢ φ
  := canonicalKripkeModel.iff_valid_provable.mp $ h _

theorem iff_provable_provable_forall_reflexive_model_validate
  : Modal.KT' α ⊢ φ ↔ (∀ {κ : Type u}, [Nonempty κ] → ∀ M : KripkeModel κ α, [Std.Refl M.rel] → M ⊧ φ)
  := by
  constructor;
  . apply forall_reflexive_model_validates_of_provable;
  . apply provable_of_forall_reflexive_model_validate;

end KT'


end LO.Modal

end

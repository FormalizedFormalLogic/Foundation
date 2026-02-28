module

public import Foundation.Modal.Kripke2.Logic.K
public import Foundation.Modal.Kripke2.Axiom.Geach

@[expose] public section

namespace LO.Modal

variable {α : Type u} {φ : Formula α}

namespace KT'

instance : Entailment.KT (Modal.KT' α) where

theorem kripke_sound : Modal.KT' _ ⊢ φ → (∀ {κ}, [Nonempty κ] → ∀ K, [Std.Refl K] → ∀ V, (⟨K, V⟩ : KripkeModel κ α) ⊧ φ) := by
  intro h κ _ F _;
  apply Hilbert.Normal2.valid_of_provable2 F ?_ h;
  rintro V _ h;
  rcases (by simpa [Hilbert.Normal2.buildAxioms] using h) with ((⟨_, _, rfl⟩ | ⟨_, rfl⟩));
  . apply KripkeModel.models_axiomK;
  . apply KripkeModel.models_axiomT_of_reflexive

theorem kripke_sound' : Modal.KT' _ ⊢ φ → (∀ {κ}, [Nonempty κ] → ∀ M : KripkeModel κ α, [Std.Refl M.rel] → M ⊧ φ)
  := fun h _ _ M _ ↦ kripke_sound h M.frame M.val

instance : Entailment.Consistent (Modal.KT' α) := by
  let K : Rel (Fin 1) (Fin 1) := (λ _ _ => True);
  have : Std.Refl K := by constructor; tauto;

  apply Hilbert.Normal2.consistent_of_valid_model' K;
  rintro V _ h;
  rcases (by simpa [Hilbert.Normal2.buildAxioms] using h) with ((⟨_, _, rfl⟩ | ⟨_, rfl⟩));
  . apply KripkeModel.models_axiomK;
  . apply KripkeModel.models_axiomT_of_reflexive

variable [DecidableEq α] [Encodable α]

theorem kripke_complete : (∀ {κ : Type u}, [Nonempty κ] → ∀ M : KripkeModel κ α, [Std.Refl M.rel] → M ⊧ φ) → Modal.KT' _ ⊢ φ
  := fun h ↦ canonicalKripkeModel.iff_valid_provable.mp $ h _

theorem iff_provable_valid_all_kripkeModel : Modal.KT' α ⊢ φ ↔ (∀ {κ : Type u}, [Nonempty κ] → ∀ M : KripkeModel κ α, [Std.Refl M.rel] → M ⊧ φ) := by
  constructor;
  . apply kripke_sound';
  . apply kripke_complete;

end KT'


end LO.Modal

end

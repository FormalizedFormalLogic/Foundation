module

public import Foundation.Modal.Hilbert.Normal2.Basic
public import Foundation.Modal.Kripke2.Basic

@[expose] public section

namespace LO.Modal

/-
namespace KripkeModel

abbrev validOnFrame (M : KripkeModel α) (φ : Formula α) :=  ∀ V, (M.replaceVal V) ⊧ φ
infix:45 " ⊧ᶠ " => validOnFrame

end KripkeModel
-/


namespace Hilbert.Normal2

open Formula

variable {κ α} [Nonempty κ] {Ax : Axiom α} {φ : Formula α}

lemma valid_of_provable2 (K) (hC : ∀ V, (⟨K, V⟩ : KripkeModel κ α).world ∀⊩* Ax)
  : Hilbert.Normal2 Ax ⊢ φ → (∀ V, (⟨K, V⟩ : KripkeModel κ α) ⊧ φ) := by
  intro hφ;
  induction hφ using Hilbert.Normal2.rec! with
  | axm hφ => intro V x; apply hC; assumption;
  | implyK | implyS | ec => grind;
  | mdp ih₁ ih₂ => intro V; exact KripkeModel.models_mdp (ih₁ V) (ih₂ V);
  | nec ih => intro V; exact KripkeModel.models_nec (ih V);

lemma consistent_of_valid_model' (K) (hV : ∀ V, (⟨K, V⟩ : KripkeModel κ α).world ∀⊩* Ax)
  : Entailment.Consistent (Hilbert.Normal2 Ax) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  by_contra! h;
  apply KripkeModel.models_falsum (M := ⟨K, λ _ _ => True⟩);
  apply valid_of_provable2 K hV h;

end Hilbert.Normal2

end LO.Modal

end

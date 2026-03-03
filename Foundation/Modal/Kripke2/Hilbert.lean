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

lemma valid_of_provable (K) (hK : ∀ V, (⟨K, V⟩ : KripkeModel κ α) ⊧* Ax)
  : Hilbert.Normal2 Ax ⊢ φ → (∀ V, (⟨K, V⟩ : KripkeModel κ α) ⊧ φ) := by
  intro hφ;
  induction hφ using Hilbert.Normal2.rec! with
  | axm hφ =>
    intro V x;
    apply hK V |>.models_set hφ;
  | implyK | implyS | ec => grind;
  | mdp ih₁ ih₂ => intro V; exact KripkeModel.validates_mdp (ih₁ V) (ih₂ V);
  | nec ih => intro V; exact KripkeModel.validates_nec (ih V);

lemma valid_of_provable2' (K) (hK : ∀ V, (⟨K, V⟩ : KripkeModel κ α) ⊧* Ax)
  : ∀ V, (⟨K, V⟩ : KripkeModel κ α) ⊧* (Hilbert.Normal2 Ax) := by
  intro V;
  constructor;
  intro φ hφ;
  apply valid_of_provable (K := K) hK $ Logic.iff_provable.mpr hφ;

lemma consistent_of_valid_model' (K) (hK : ∀ V, (⟨K, V⟩ : KripkeModel κ α) ⊧* Ax)
  : Entailment.Consistent (Hilbert.Normal2 Ax) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  by_contra! h;
  apply KripkeModel.validates_falsum (M := ⟨K, λ _ _ => True⟩);
  apply valid_of_provable K hK h;

/-
#check Semantics.Meaningful

lemma consistent_of_valid_model'
  (P : ∀ {κ : Type v}, [Nonempty κ] → Rel κ κ → Prop)
  {κ : Type v} [Nonempty κ] (K : Rel κ κ) (hP : P K)
  (S : ∀ φ, (Hilbert.Normal2 Ax) ⊢ φ → (∀ {κ : Type v}, [Nonempty κ] → ∀ K, P K → ∀ V, (⟨K, V⟩ : KripkeModel κ α) ⊧ φ))
  : Entailment.Consistent (Hilbert.Normal2 Ax) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  by_contra! h;
  have := @S ⊥ h κ _ K hP (λ _ _ => True);
  sorry;
-/

end Hilbert.Normal2

end LO.Modal

end

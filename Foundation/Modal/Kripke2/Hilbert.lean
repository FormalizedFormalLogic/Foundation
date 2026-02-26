module

public import Foundation.Modal.Hilbert.Normal.Basic
public import Foundation.Modal.Kripke2.Basic

@[expose] public section

namespace LO.Modal

/-
namespace KripkeModel

abbrev validOnFrame (M : KripkeModel α) (φ : Formula α) :=  ∀ V, (M.replaceVal V) ⊧ φ
infix:45 " ⊧ᶠ " => validOnFrame

end KripkeModel
-/


namespace Hilbert.Normal

open Formula

variable {α : Type u} {β : Type v} {Ax : Axiom α} {φ : Formula α}

lemma valid_of_provable (M : KripkeModel.{u, v} α) (hC : ∀ V, (M.replaceVal V) ∀⊩* Ax)
  : Hilbert.Normal Ax ⊢ φ → (∀ V, (M.replaceVal V) ⊧ φ) := by
  intro hφ;
  induction hφ using Hilbert.Normal.rec! with
  | @axm φ s hφ =>
    intro V x;
    apply KripkeModel.iff_forces_replaceSubstVal s |>.mp;
    suffices (M.replaceVal (fun a x ↦ x ⊩ s a)).Forces x φ by tauto;
    exact hC (fun a x ↦ x ⊩ s a) φ hφ x;
  | implyK | implyS | ec => grind;
  | mdp ih₁ ih₂ => intro V; exact KripkeModel.models_mdp (ih₁ V) (ih₂ V);
  | nec ih => intro V; exact KripkeModel.models_nec (ih V);

lemma consistent_of_valid_model
  (M : KripkeModel.{u, v} α) (hV : ∀ V, M.replaceVal V ∀⊩* Ax)
  : Entailment.Consistent (Hilbert.Normal Ax) := by
  apply Entailment.Consistent.of_unprovable (φ := ⊥);
  by_contra! h;
  apply KripkeModel.models_falsum (M := M);
  apply valid_of_provable (M := M) hV h;

end Hilbert.Normal

end LO.Modal

end

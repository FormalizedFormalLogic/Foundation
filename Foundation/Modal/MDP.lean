import Foundation.Modal.System
import Foundation.Logic.Disjunctive

namespace LO.System

variable {F : Type*} [LogicalConnective F] [Box F]
variable {S : Type*} [System F S]

class ModalDisjunctive (𝓢 : S) : Prop where
  modal_disjunctive : ∀ {φ ψ : F}, 𝓢 ⊢! □φ ⋎ □ψ → 𝓢 ⊢! φ ∨ 𝓢 ⊢! ψ

alias modal_disjunctive := ModalDisjunctive.modal_disjunctive

variable {𝓢 : S} [System.Minimal 𝓢]

instance [Disjunctive 𝓢] [Unnecessitation 𝓢] : ModalDisjunctive 𝓢 where
  modal_disjunctive h := by
    rcases disjunctive h with (h | h);
    . left; exact unnec! h;
    . right; exact unnec! h;

private lemma unnec_of_mdp_aux [ModalDisjunctive 𝓢] (h : 𝓢 ⊢! □φ) : 𝓢 ⊢! φ := by
    have : 𝓢 ⊢! □φ ⋎ □φ := or₁'! h;
    rcases modal_disjunctive this with (h | h) <;> tauto;

noncomputable instance unnecessitation_of_modalDisjunctive [ModalDisjunctive 𝓢] : Unnecessitation 𝓢 where
  unnec h := (unnec_of_mdp_aux ⟨h⟩).some

end LO.System

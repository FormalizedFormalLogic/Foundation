import Foundation.Modal.System
import Foundation.Logic.Disjunctive

namespace LO.System

variable {F : Type*} [LogicalConnective F] [Box F]
variable {S : Type*} [System F S]

class ModalDisjunctive (𝓢 : S) : Prop where
  modal_disjunctive : ∀ {p q : F}, 𝓢 ⊢! □p ⋎ □q → 𝓢 ⊢! p ∨ 𝓢 ⊢! q

alias modal_disjunctive := ModalDisjunctive.modal_disjunctive

variable {𝓢 : S} [System.Minimal 𝓢]

instance [Disjunctive 𝓢] [Unnecessitation 𝓢] : ModalDisjunctive 𝓢 where
  modal_disjunctive h := by
    rcases disjunctive h with (h | h);
    . left; exact unnec! h;
    . right; exact unnec! h;

private lemma unnec_of_mdp_aux [ModalDisjunctive 𝓢] (h : 𝓢 ⊢! □p) : 𝓢 ⊢! p := by
    have : 𝓢 ⊢! □p ⋎ □p := or₁'! h;
    rcases modal_disjunctive this with (h | h) <;> tauto;

noncomputable instance unnecessitation_of_modalDisjunctive [ModalDisjunctive 𝓢] : Unnecessitation 𝓢 where
  unnec h := (unnec_of_mdp_aux ⟨h⟩).some

end LO.System

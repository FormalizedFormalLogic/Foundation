import Foundation.Modal.Entailment.E

namespace LO.Modal.Entailment

open LO.Entailment LO.Entailment.FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment F S]
variable {𝓢 : S} [Entailment.ET 𝓢] {n : ℕ} {φ ψ ξ χ: F}

variable [DecidableEq F]

def diabot! : 𝓢 ⊢! ◇⊤ := by
  apply M!_of_NLN!;
  exact (CCNCN ⨀ axiomT) ⨀ verum;
lemma diabot : 𝓢 ⊢ ◇⊤ := ⟨diabot!⟩

end LO.Modal.Entailment

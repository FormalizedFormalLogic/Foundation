module

public import Foundation.Modal.Entailment.E

@[expose] public section

namespace LO.Modal.Entailment

open LO.Entailment LO.Entailment.FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment S F]
variable {𝓢 : S} [Entailment.ET 𝓢] {n : ℕ} {φ ψ ξ χ: F}

variable [DecidableEq F]

def diabot! : 𝓢 ⊢! ◇⊤ := by
  apply M!_of_NLN!;
  exact (CCNCN ⨀ axiomT) ⨀ verum;
lemma diabot : 𝓢 ⊢ ◇⊤ := ⟨diabot!⟩

namespace ET

instance : Entailment.HasAxiomD 𝓢 := ⟨C_trans axiomT diaTc⟩

instance : Entailment.ED 𝓢 where

end ET

end LO.Modal.Entailment
end

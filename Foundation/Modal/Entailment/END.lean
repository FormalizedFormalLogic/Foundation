module

public import Foundation.Modal.Entailment.K
public import Foundation.Modal.Entailment.EN

@[expose] public section

namespace LO.Modal.Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment S F]
variable {𝓢 : S}

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

protected class END (𝓢 : S) extends Entailment.EN 𝓢, HasAxiomD 𝓢

instance [Entailment.END 𝓢] : HasAxiomP 𝓢 := ⟨by
  have : 𝓢 ⊢! ∼∼□(∼⊥) := dni' $ nec NO;
  have : 𝓢 ⊢! ∼◇⊥ := (contra $ K_left diaDuality) ⨀ this;
  exact (contra axiomD) ⨀ this;
⟩

end LO.Modal.Entailment
end

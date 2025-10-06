import Foundation.Modal.Entailment.ET
import Foundation.Modal.Entailment.EN

namespace LO.Modal.Entailment

open LO.Entailment LO.Entailment.FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment F S]
variable {𝓢 : S} {n : ℕ} {φ ψ ξ χ: F}

protected class ET5 (𝓢 : S) extends Entailment.E 𝓢, HasAxiomT 𝓢, HasAxiomFive 𝓢
instance [Entailment.ET5 𝓢] : Entailment.ET 𝓢 where
instance [Entailment.ET5 𝓢] : Entailment.E5 𝓢 where


variable [Entailment.ET5 𝓢]
variable [DecidableEq F]

namespace ET5

instance : Entailment.HasAxiomN 𝓢 := ⟨by
  have H₁ : 𝓢 ⊢! ◇⊤ ➝ □◇⊤ := axiomFive;
  have H₂ : 𝓢 ⊢! □◇⊤ ➝ □⊤ := K_left $ re $ iff_top_left' $ diabot!;
  exact (C_trans H₁ H₂) ⨀ diabot!;
⟩

instance : Entailment.EN 𝓢 where

end ET5


end LO.Modal.Entailment

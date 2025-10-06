import Foundation.Modal.Entailment.ET
import Foundation.Modal.Entailment.EN

namespace LO.Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment F S] {𝓢 : S} [Entailment.Minimal 𝓢]

def C_of (h : 𝓢 ⊢! φ) : 𝓢 ⊢! ψ ➝ φ := deduct' $ of h
@[grind] lemma C_of! : 𝓢 ⊢ φ → 𝓢 ⊢ ψ ➝ φ := λ ⟨h⟩ => ⟨C_of h⟩

end LO.Entailment


namespace LO.Modal.Entailment

open LO.Entailment LO.Entailment.FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [Entailment F S]
variable {𝓢 : S} {n : ℕ} {φ ψ ξ χ: F}


section

end


protected class ETB (𝓢 : S) extends Entailment.E 𝓢, HasAxiomT 𝓢, HasAxiomB 𝓢
instance [Entailment.ETB 𝓢] : Entailment.ET 𝓢 where
instance [Entailment.ETB 𝓢] : Entailment.EB 𝓢 where


variable [Entailment.ETB 𝓢]
variable [DecidableEq F]

namespace ETB

instance : Entailment.Necessitation 𝓢 := ⟨by
  intro φ h;
  exact (K_right $ re $ K_intro diaTc (C_of h)) ⨀ (axiomB ⨀ h);
⟩

instance : Entailment.HasAxiomN 𝓢 := inferInstance

instance : Entailment.EN 𝓢 where

end ETB


end LO.Modal.Entailment

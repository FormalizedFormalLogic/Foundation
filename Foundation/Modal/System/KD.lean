import Foundation.Modal.System.K

namespace LO.System

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [System F S]
variable {𝓢 : S} [System.KD 𝓢]

namespace KD

protected def axiomP : 𝓢 ⊢ Axioms.P := by
  have : 𝓢 ⊢ ∼∼□(∼⊥) := dni' $ nec notbot;
  have : 𝓢 ⊢ ∼◇⊥ := (contra₀' $ and₁' diaDuality) ⨀ this;
  exact (contra₀' axiomD) ⨀ this;
instance : HasAxiomP 𝓢 := ⟨KD.axiomP⟩

end KD

end LO.System

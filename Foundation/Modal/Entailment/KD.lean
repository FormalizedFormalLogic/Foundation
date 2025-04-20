import Foundation.Modal.Entailment.K

namespace LO.Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.Modal.KD 𝓢]

namespace KD

protected def axiomP : 𝓢 ⊢ Axioms.P := by
  have : 𝓢 ⊢ ∼∼□(∼⊥) := dni' $ nec NO;
  have : 𝓢 ⊢ ∼◇⊥ := (contra $ K_left diaDuality) ⨀ this;
  exact (contra axiomD) ⨀ this;
instance : HasAxiomP 𝓢 := ⟨KD.axiomP⟩

end KD

end LO.Entailment

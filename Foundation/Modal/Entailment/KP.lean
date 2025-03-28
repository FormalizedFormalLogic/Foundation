import Foundation.Modal.Entailment.K

namespace LO.Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.Modal.KP 𝓢]

namespace KP

protected def axiomD [HasDiaDuality 𝓢] : 𝓢 ⊢ Axioms.D φ := by
  have : 𝓢 ⊢ φ ➝ (∼φ ➝ ⊥) := impTrans'' dni (and₁' neg_equiv);
  have : 𝓢 ⊢ □φ ➝ □(∼φ ➝ ⊥) := implyBoxDistribute' this;
  have : 𝓢 ⊢ □φ ➝ (□(∼φ) ➝ □⊥) := impTrans'' this axiomK;
  have : 𝓢 ⊢ □φ ➝ (∼□⊥ ➝ ∼□(∼φ)) := impTrans'' this contra₀;
  have : 𝓢 ⊢ □φ ➝ ∼□(∼φ) := impSwap' this ⨀ axiomP;
  exact impTrans'' this (and₂' diaDuality);
instance : HasAxiomD 𝓢 := ⟨fun _ ↦ KP.axiomD⟩

end KP

end LO.Entailment

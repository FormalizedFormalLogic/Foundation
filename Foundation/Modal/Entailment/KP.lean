import Foundation.Modal.Entailment.K

namespace LO.Entailment

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.Modal.KP 𝓢]

namespace KP

protected def axiomD [HasDiaDuality 𝓢] : 𝓢 ⊢ Axioms.D φ := by
  have : 𝓢 ⊢ φ ➝ (∼φ ➝ ⊥) := cTrans dni (φOfKφψ negEquiv);
  have : 𝓢 ⊢ □φ ➝ □(∼φ ➝ ⊥) := implyBoxDistribute' this;
  have : 𝓢 ⊢ □φ ➝ (□(∼φ) ➝ □⊥) := cTrans this axiomK;
  have : 𝓢 ⊢ □φ ➝ (∼□⊥ ➝ ∼□(∼φ)) := cTrans this contra₀;
  have : 𝓢 ⊢ □φ ➝ ∼□(∼φ) := impSwap' this ⨀ axiomP;
  exact cTrans this (ψOfKφψ diaDuality);
instance : HasAxiomD 𝓢 := ⟨fun _ ↦ KP.axiomD⟩

end KP

end LO.Entailment

module

public import Foundation.Modal.Entailment.K

@[expose] public section

namespace LO.Modal.Entailment

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment S F]
variable {𝓢 : S} [Entailment.KP 𝓢]

namespace KP

protected def axiomD [HasDiaDuality 𝓢] : 𝓢 ⊢! Axioms.D φ := by
  have : 𝓢 ⊢! φ ➝ (∼φ ➝ ⊥) := C_trans dni (K_left negEquiv);
  have : 𝓢 ⊢! □φ ➝ □(∼φ ➝ ⊥) := implyBoxDistribute' this;
  have : 𝓢 ⊢! □φ ➝ (□(∼φ) ➝ □⊥) := C_trans this axiomK;
  have : 𝓢 ⊢! □φ ➝ (∼□⊥ ➝ ∼□(∼φ)) := C_trans this CCCNN;
  have : 𝓢 ⊢! □φ ➝ ∼□(∼φ) := C_swap this ⨀ axiomP;
  exact C_trans this (K_right diaDuality);
instance : HasAxiomD 𝓢 := ⟨KP.axiomD⟩

end KP

end LO.Modal.Entailment
end

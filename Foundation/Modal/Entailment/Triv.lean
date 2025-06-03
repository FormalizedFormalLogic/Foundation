import Foundation.Modal.Entailment.KT
import Foundation.Modal.Entailment.KTc

namespace LO.Modal.Entailment

open LO.Entailment LO.Entailment.FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment F S]
variable {𝓢 : S} [Entailment.Triv 𝓢]

namespace Triv

protected def axiomGrz : 𝓢 ⊢ □(□(φ ➝ □φ) ➝ φ) ➝ φ := by
  have : 𝓢 ⊢ φ ➝ □φ := axiomTc;
  have d₁ := nec this;
  have d₂ : 𝓢 ⊢ □(φ ➝ □φ) ➝ ((□(φ ➝ □φ)) ➝ φ) ➝ φ := CCC;
  have := d₂ ⨀ d₁;
  exact C_trans axiomT this;
instance : HasAxiomGrz 𝓢 := ⟨fun _ ↦ Triv.axiomGrz⟩

end Triv

end LO.Modal.Entailment

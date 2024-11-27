import Foundation.Modal.System.KT
import Foundation.Modal.System.KTc

namespace LO.System

open FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [System F S]
variable {𝓢 : S} [System.Triv 𝓢]

namespace Triv

protected def axiomGrz : 𝓢 ⊢ □(□(φ ➝ □φ) ➝ φ) ➝ φ := by
  have : 𝓢 ⊢ φ ➝ □φ := axiomTc;
  have d₁ := nec this;
  have d₂ : 𝓢 ⊢ □(φ ➝ □φ) ➝ ((□(φ ➝ □φ)) ➝ φ) ➝ φ := p_pq_q;
  have := d₂ ⨀ d₁;
  exact impTrans'' axiomT this;
instance : HasAxiomGrz 𝓢 := ⟨fun _ ↦ Triv.axiomGrz⟩

end Triv

end LO.System

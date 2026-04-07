module

public import Foundation.Modal.Entailment.KT
public import Foundation.Modal.Entailment.KTc

@[expose] public section

namespace LO.Modal.Entailment

open LO.Entailment LO.Entailment.FiniteContext

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment S F]
variable {𝓢 : S} [Entailment.Triv 𝓢]

noncomputable instance : HasAxiomGrz 𝓢 := ⟨by
  intro φ;
  have : 𝓢 ⊢! φ 🡒 □φ := axiomTc;
  have d₁ := nec this;
  have d₂ : 𝓢 ⊢! □(φ 🡒 □φ) 🡒 ((□(φ 🡒 □φ)) 🡒 φ) 🡒 φ := CCC;
  have := d₂ ⨀ d₁;
  exact C_trans axiomT this;
⟩

end LO.Modal.Entailment
end

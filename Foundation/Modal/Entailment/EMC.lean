module

public import Foundation.Modal.Entailment.EM

@[expose] public section

namespace LO.Modal.Entailment

open LO.Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment S F]
variable {𝓢 : S}

instance [Entailment.EMC 𝓢] : Entailment.HasAxiomK 𝓢 where
  K φ ψ := by
    haveI h₁ : 𝓢 ⊢! (□(φ 🡒 ψ) ⋏ □φ) 🡒 □((φ 🡒 ψ) ⋏ φ) := axiomC;
    haveI h₂ : 𝓢 ⊢! ((φ 🡒 ψ) ⋏ φ) 🡒 ψ := C_trans CKK innerMDP
    haveI h₃ : 𝓢 ⊢! □((φ 🡒 ψ) ⋏ φ) 🡒 □ψ := rm h₂;
    haveI h₄ : 𝓢 ⊢! □(φ 🡒 ψ) ⋏ □φ 🡒 □ψ := C_trans h₁ h₃;
    exact CC_of_CK h₄

end LO.Modal.Entailment
end

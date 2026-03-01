module

public import Foundation.Modal.Entailment.Basic

@[expose] public section

namespace LO.Modal.Entailment

open LO.Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment S F]
variable {𝓢 : S}

section

instance [Entailment.EM 𝓢] : Entailment.RM 𝓢 := ⟨by
  intro φ ψ h;
  haveI h₁ : 𝓢 ⊢! φ ⭤ (φ ⋏ ψ) := K_intro (CK_of_C_of_C C_id h) and₁
  haveI h₂ : 𝓢 ⊢! □φ ⭤ □(φ ⋏ ψ) := re h₁;
  haveI h₃ : 𝓢 ⊢! □φ ➝ □(φ ⋏ ψ) := K_left h₂;
  haveI h₄ : 𝓢 ⊢! □(φ ⋏ ψ) ➝ (□φ ⋏ □ψ) := axiomM;
  haveI h₅ : 𝓢 ⊢! □φ ➝ □φ ⋏ □ψ := C_trans h₃ h₄;
  apply C_trans h₅ and₂;
⟩

instance [Entailment.E 𝓢] [Entailment.RM 𝓢] : Entailment.EM 𝓢 where
  M := by
    intro φ ψ;
    apply CK_of_C_of_C;
    . apply rm; exact and₁;
    . apply rm; exact and₂;

end

end LO.Modal.Entailment
end

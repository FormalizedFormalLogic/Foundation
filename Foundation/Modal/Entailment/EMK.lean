module

public import Foundation.Modal.Entailment.EM
public import Foundation.Meta.ClProver

@[expose] public section

namespace LO.Modal.Entailment

variable {S F : Type*} [BasicModalLogicalConnective F] [DecidableEq F] [Entailment S F]
variable {𝓢 : S}

open LO.Entailment LO.Entailment.FiniteContext LO.Modal.Entailment

protected class EMK (𝓢 : S) extends Entailment.EM 𝓢, HasAxiomK 𝓢

instance [Entailment.EMK 𝓢] : HasAxiomC 𝓢 := ⟨by
  intro φ ψ;
  apply deduct';
  have H₁ : [□φ ⋏ □ψ] ⊢[𝓢]! □(ψ 🡒 (φ ⋏ ψ)) 🡒 □ψ 🡒 □(φ ⋏ ψ) := axiomK;
  have H₂ : [□φ ⋏ □ψ] ⊢[𝓢]! □φ := K_left $ FiniteContext.byAxm (φ := □φ ⋏ □ψ) (by simp);
  have H₃ : [□φ ⋏ □ψ] ⊢[𝓢]! □ψ := K_right $ FiniteContext.byAxm (φ := □φ ⋏ □ψ) (by simp);
  apply H₁ ⨀ ?_ ⨀ H₃;
  have H₄ : [□φ ⋏ □ψ] ⊢[𝓢]! □(ψ 🡒 φ) := (of $ rm $ implyK) ⨀ H₂;
  have H₅ : [□φ ⋏ □ψ] ⊢[𝓢]! □(ψ 🡒 φ) 🡒 □(ψ 🡒 (φ ⋏ ψ)) := of $ by
    apply K_left;
    apply re;
    apply E_intro;
    . apply deduct';
      apply deduct;
      apply K_intro;
      . have H₅₁ : [ψ, ψ 🡒 φ] ⊢[𝓢]! ψ := FiniteContext.byAxm (by simp);
        have H₅₂ : [ψ, ψ 🡒 φ] ⊢[𝓢]! ψ 🡒 φ := FiniteContext.byAxm (by simp);
        exact H₅₂ ⨀ H₅₁;
      . apply FiniteContext.byAxm;
        simp;
    . apply deduct';
      apply deduct;
      have H₅₁ : [ψ, ψ 🡒 φ ⋏ ψ] ⊢[𝓢]! ψ := FiniteContext.byAxm (by simp);
      have H₅₂ : [ψ, ψ 🡒 φ ⋏ ψ] ⊢[𝓢]! ψ 🡒 φ ⋏ ψ := FiniteContext.byAxm (by simp);
      exact K_left $ H₅₂ ⨀ H₅₁;
  exact H₅ ⨀ H₄;
⟩

end LO.Modal.Entailment
end

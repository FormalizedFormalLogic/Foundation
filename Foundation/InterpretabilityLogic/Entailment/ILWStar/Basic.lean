import Foundation.InterpretabilityLogic.Entailment.ILW

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S} {φ ψ χ : F}

protected class ILWStar (𝓢 : S) extends InterpretabilityLogic.Entailment.IL 𝓢, HasAxiomWStar 𝓢

variable [Entailment.ILWStar 𝓢]

instance : Entailment.HasAxiomW 𝓢 := by
  constructor;
  intro φ ψ;
  sorry;
  /-
  apply deduct';


  have H₁ : [φ ▷ ψ] ⊢[𝓢]! (ψ ⋏ □φ) ▷ (ψ ⋏ □φ ⋏ □(∼φ)) := deductInv' $ WStar!;
  have H₂ : [φ ▷ ψ] ⊢[𝓢]! (ψ ⋏ □φ ⋏ □(∼φ)) ▷ (ψ ⋏ □(∼φ)) := of $ by
    refine J1! ⨀ ?_;
    apply nec;
    apply deduct';
    suffices [ψ, □φ, □(∼φ)] ⊢[𝓢]! ψ ⋏ □(∼φ) by tauto;
    apply K_intro <;>
    . apply FiniteContext.byAxm;
      simp;
  have H₃ : [φ ▷ ψ] ⊢[𝓢]! (ψ ⋏ □φ) ▷ (ψ ⋏ □(∼φ)) := by sorry;

  have H₄ : [φ ▷ ψ] ⊢[𝓢]! (ψ ▷ χ) ➝ (φ ▷ χ) := deductInv' J2!;


  apply C_trans $ WStar! (ψ := ψ) (χ := φ);

  apply CRhdRhd!_of_C!_C!;
  . sorry;
  . apply deduct';
    suffices [ψ, □ψ, □(∼φ)] ⊢[𝓢]! ψ ⋏ □(∼φ) by tauto;
    apply K_intro <;>
    . apply FiniteContext.byAxm;
      simp;
  -/

end LO.InterpretabilityLogic.Entailment

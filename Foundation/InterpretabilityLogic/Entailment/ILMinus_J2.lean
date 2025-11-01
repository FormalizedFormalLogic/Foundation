import Foundation.InterpretabilityLogic.Entailment.ILMinus_J4

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S}

protected class ILMinus_J2 (𝓢 : S) extends Entailment.ILMinus 𝓢, HasAxiomJ2 𝓢

section

variable [Entailment.ILMinus_J2 𝓢]

instance : HasAxiomJ4' 𝓢 := ⟨by
  intro φ ψ;
  apply J2!;
⟩

end


protected class ILMinus_J2Plus (𝓢 : S) extends Entailment.ILMinus 𝓢, HasAxiomJ2Plus 𝓢

section

variable [Entailment.ILMinus_J2Plus 𝓢]

instance : HasAxiomJ2Plus' 𝓢 := ⟨by
  intro A B C;
  dsimp only [Axioms.J2Plus'];

  sorry;
⟩

instance : HasAxiomJ2 𝓢 := ⟨by
  intro φ ψ χ;
  apply C_trans ?_ J2Plus!;
  apply R1!;
  apply or₁;
⟩

instance : HasAxiomJ4Plus 𝓢 := ⟨by
  intro φ ψ χ;
  dsimp only [Axioms.J4Plus];
  have : 𝓢 ⊢! □(φ ➝ ψ) ➝ □(∼(φ ⋏ ψ)) := by
    apply box_regularity;
    sorry;
  have : 𝓢 ⊢! □(φ ➝ ψ) ➝ ((φ ⋏ ψ) ▷ ψ) := C_trans this CLNRhd!;
  sorry;
⟩

end


protected class ILMinus_J1_J2 (𝓢 : S) extends Entailment.ILMinus 𝓢, HasAxiomJ1 𝓢, HasAxiomJ2 𝓢

section

variable [Entailment.ILMinus_J2 𝓢]

instance : HasAxiomJ2Plus 𝓢 := ⟨by
  intro φ ψ χ;
  apply deduct';
  have : [φ ▷ (ψ ⋎ χ)] ⊢[𝓢]! (ψ ▷ χ) ➝ ((ψ ⋎ χ) ▷ χ) := of $ R2! or₁;
  have : [φ ▷ (ψ ⋎ χ)] ⊢[𝓢]! ((ψ ⋎ χ) ▷ χ) ➝ (φ ▷ χ) := deductInv' $ J2!;
  apply C_trans (of $ R2! or₁) $ deductInv' $ J2!;
⟩

end

end LO.InterpretabilityLogic.Entailment

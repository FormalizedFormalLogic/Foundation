module

public import Foundation.InterpretabilityLogic.Entailment.ILMinus

@[expose] public section

namespace LO.InterpretabilityLogic.Entailment

open LO.Entailment LO.Modal.Entailment
open FiniteContext

variable {S F : Type*} [DecidableEq F] [InterpretabilityLogicalConnective F] [Entailment S F] {𝓢 : S}

protected class ILMinus_J4 (𝓢 : S) extends Entailment.ILMinus 𝓢, HasAxiomJ4 𝓢

section

variable [Entailment.ILMinus_J4 𝓢]

instance : HasAxiomJ4' 𝓢 := ⟨λ {_ _} ↦ C_trans axiomJ4! CCMMCRhdORhdO!⟩

end


protected class ILMinus_J4' (𝓢 : S) extends Entailment.ILMinus 𝓢, HasAxiomJ4' 𝓢

section

variable [Entailment.ILMinus_J4' 𝓢]

instance : HasAxiomJ4 𝓢 := ⟨fun {_ _} ↦ C_trans axiomJ4'! CCRhdORhdOCMM!⟩

end



protected class ILMinus_J4Plus (𝓢 : S) extends Entailment.ILMinus 𝓢, HasAxiomJ4Plus 𝓢

section

variable [Entailment.ILMinus_J4Plus 𝓢]

instance : HasAxiomJ4' 𝓢 := ⟨by
  intro φ ψ;
  have : 𝓢 ⊢! (∼∼ψ ▷ ⊥) ➝ □(ψ ➝ ⊥) := C_trans CRhdNOL! $ box_regularity $ K_left negEquiv;
  have : 𝓢 ⊢! (ψ ▷ ⊥) ➝ □(ψ ➝ ⊥) := C_trans (R2! dne) this;
  apply C_swap $ C_trans this $ axiomJ4Plus!;
⟩

instance : HasAxiomJ4Plus' 𝓢 := ⟨by
  intro φ ψ χ;
  apply C_trans (box_regularity CCC) $ axiomJ4Plus!;
⟩

end


protected class ILMinus_J4Plus' (𝓢 : S) extends Entailment.ILMinus 𝓢, HasAxiomJ4Plus' 𝓢

section

variable [Entailment.ILMinus_J4Plus' 𝓢]

instance : HasAxiomJ4Plus'' 𝓢 := ⟨by
  intro A B C;
  apply C_trans (show 𝓢 ⊢! □A ➝ (C ▷ (A ➝ A ⋏ B) ➝ C ▷ (A ⋏ B)) by exact axiomJ4Plus'!);
  apply deduct';
  apply C_trans (show [C ▷ (A ➝ A ⋏ B) ➝ C ▷ (A ⋏ B)] ⊢[𝓢]! C ▷ B ➝ C ▷ (A ➝ A ⋏ B) by exact of $ R1! $ C_swap $ and₃);
  apply FiniteContext.byAxm;
  simp;
⟩

end


protected class ILMinus_J4Plus'' (𝓢 : S) extends Entailment.ILMinus 𝓢, HasAxiomJ4Plus'' 𝓢

section

variable [Entailment.ILMinus_J4Plus'' 𝓢]

instance : HasAxiomJ4Plus 𝓢 := ⟨by
  intro φ ψ χ;
  have H₁ : 𝓢 ⊢! □(φ ➝ ψ) ➝ χ ▷ φ ➝ χ ▷ ((φ ➝ ψ) ⋏ φ) := axiomJ4Plus''!;
  have H₂ : 𝓢 ⊢! χ ▷ ((φ ➝ ψ) ⋏ φ) ➝ χ ▷ ψ := R1! $ C_trans CKK $ innerMDP;
  exact CC!_of_CC!_of_C! H₁ H₂;
⟩

end


instance [Entailment.ILMinus_J4 𝓢] : Entailment.ILMinus_J4' 𝓢 where
instance [Entailment.ILMinus_J4' 𝓢] : Entailment.ILMinus_J4 𝓢 where

instance [Entailment.ILMinus_J4Plus 𝓢] : Entailment.ILMinus_J4Plus' 𝓢 where
instance [Entailment.ILMinus_J4Plus' 𝓢] : Entailment.ILMinus_J4Plus'' 𝓢 where
instance [Entailment.ILMinus_J4Plus'' 𝓢] : Entailment.ILMinus_J4Plus 𝓢 where

instance [Entailment.ILMinus_J4Plus 𝓢] : Entailment.ILMinus_J4' 𝓢 where
instance [Entailment.ILMinus_J4Plus 𝓢] : Entailment.ILMinus_J4 𝓢 where

end LO.InterpretabilityLogic.Entailment
end
